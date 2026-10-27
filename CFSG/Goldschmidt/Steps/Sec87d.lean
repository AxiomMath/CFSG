module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec8LemmaA
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.PropHSetup
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem inf_center_ne_bot' {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem oddCoreOf_top_eq_bot (hset : GoldSetting G S A) : oddCoreOf (⊤ : Subgroup G) = ⊥ := by
  have := hset.isSimpleGroup
  have hN : (oddCoreOf (⊤ : Subgroup G)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_oddCoreOf ⊤))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCoreOf (⊤ : Subgroup G)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
    have hodd := odd_card_oddCoreOf (⊤ : Subgroup G)
    rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card G := by
      have := orderOf_dvd_natCard a
      rwa [orderOf_eq_prime (hset.elem.2 a ha) ha1] at this
    exact hodd.not_two_dvd_nat h2

theorem conj_eq_of_mem_centralizer' (hset : GoldSetting G S A) {u : G} (hu2 : u ^ 2 = 1)
    (huZ : u ∈ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (hd : ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), u * (n⁻¹ * u * n) ∈ A) {m : G}
    (hm : m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hmA : m ∈ Subgroup.centralizer (A : Set G)) : m⁻¹ * u * m = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G) with hN
  set e := u * (m⁻¹ * u * m) with he
  have heA : e ∈ A := hd m hm
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  have hme : m⁻¹ * u * m = u * e := by
    rw [he, ← mul_assoc, huu, one_mul]
  have hpow : ∀ j : ℕ, (m ^ j)⁻¹ * u * m ^ j = u * e ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : m⁻¹ * e ^ j * m = e ^ j := by
        rw [mul_assoc, Subgroup.mem_centralizer_iff.mp hmA _ (A.pow_mem heA j),
          ← mul_assoc, inv_mul_cancel, one_mul]
      calc (m ^ (j + 1))⁻¹ * u * m ^ (j + 1) = m⁻¹ * ((m ^ j)⁻¹ * u * m ^ j) * m := by
            rw [pow_succ]; group
        _ = (m⁻¹ * u * m) * (m⁻¹ * e ^ j * m) := by rw [ih]; group
        _ = u * e ^ (j + 1) := by rw [hme, hc, pow_succ']; group
  set k := ((S : Subgroup G).subgroupOf N).index with hk
  have hkodd : ¬ 2 ∣ k := fun h => Sylow.not_dvd_index S
    (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  have hmk : m ^ k ∈ (S : Subgroup G) := by
    have hnormal : ((S : Subgroup G).subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have h1 : (QuotientGroup.mk (⟨m, hm⟩ : N) : N ⧸ (S : Subgroup G).subgroupOf N) ^ k = 1 :=
      pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have h2 : (m ^ k)⁻¹ * u * m ^ k = u := by
    rw [mul_assoc, ← Subgroup.mem_centralizer_iff.mp huZ _ hmk, ← mul_assoc, inv_mul_cancel,
      one_mul]
  rw [hpow] at h2
  have hek : e ^ k = 1 := mul_left_cancel (h2.trans (mul_one u).symm)
  have he2 : e ^ 2 = 1 := hset.elem.2 e heA
  have he1 : e = 1 := by
    obtain ⟨q, hq⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    rw [hq, pow_succ, pow_mul, he2, one_pow, one_mul] at hek
    exact hek
  rw [hme, he1, mul_one]

theorem eq_omega1_center (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hC1 : ∀ u ∈ (S : Subgroup G), ∀ v ∈ (S : Subgroup G), u ^ 2 = 1 → v ^ 2 = 1 →
      u * v = v * u → u ∉ A → v ∉ A → u * v ∈ A) :
    A = Omega1 ((S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSA : (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := le_centralizer hset h4
  have hAZ : A ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp hSA
  refine le_antisymm (fun c hc => ?_) ?_
  · show c ∈ Subgroup.closure _
    exact Subgroup.subset_closure ⟨⟨hset.le hc, hAZ hc⟩, hset.elem.2 c hc⟩
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨⟨huS, huZ⟩, hu2⟩ := hu
  by_contra huA
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  have hNA := normalizer_le_normalizer hset
  have hcen : ∀ w ∈ (S : Subgroup G), w ^ 2 = 1 →
      (S : Subgroup G) ≤ Subgroup.centralizer ({w} : Set G) := by
    intro w hw hw2
    by_cases hwA : w ∈ A
    · exact hSA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwA))
    have huw := hC1 u huS w hw hu2 hw2 (Subgroup.mem_centralizer_iff.mp huZ w hw).symm huA hwA
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : w = u * (u * w) := by rw [← mul_assoc, huu, one_mul]
    have h1 := Subgroup.mem_centralizer_iff.mp huZ s hs
    have h2 := Subgroup.mem_centralizer_iff.mp (hSA hs) _ huw
    rw [e]
    calc s * (u * (u * w)) = (s * u) * (u * w) := by group
      _ = (u * s) * (u * w) := by rw [h1]
      _ = u * ((u * w) * s) := by rw [mul_assoc, h2]
      _ = u * (u * w) * s := by group
  have hd : ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), u * (n⁻¹ * u * n) ∈ A := by
    intro n hn
    have hwS : n⁻¹ * u * n ∈ (S : Subgroup G) := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) u).mp huS
    have hw2 : (n⁻¹ * u * n) ^ 2 = 1 := by simpa using conj_sq_eq_one (g := n⁻¹) hu2
    have hwA : n⁻¹ * u * n ∉ A := fun h => huA (by
      have := conj_mem (hNA hn) h
      simpa [mul_assoc] using this)
    exact hC1 u huS _ hwS hu2 hw2 (Subgroup.mem_centralizer_iff.mp huZ _ hwS).symm huA hwA
  have hfixC : ∀ m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      m ∈ Subgroup.centralizer (A : Set G) → m⁻¹ * u * m = u := fun m hm hmA =>
    conj_eq_of_mem_centralizer' hset hu2 huZ hd hm hmA
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
  obtain ⟨x, hxS, hxaA, hxa⟩ := exists_mem_normalizer_sylow hset h4 ha ha1
  have hxA : x⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ (hNA hxS)
  have hxC : x⁻¹ ∉ Subgroup.centralizer (A : Set G) := fun h => hxa (by
    have := conj_eq_of_mem_centralizer h ha
    simpa using this)
  have hσ : ∀ c ∈ A, c ≠ 1 → x⁻¹ * (x⁻¹ * c * x) * x = c * (x⁻¹ * c * x) := fun c hc hc1 => by
    simpa using (conj_conj_eq_mul hset h4 hxA hxC hc hc1).2
  set ex := u * (x⁻¹ * u * x) with hex
  have hexA : ex ∈ A := hd x hxS
  have hxux : x⁻¹ * u * x = u * ex := by rw [hex, ← mul_assoc, huu, one_mul]
  obtain ⟨c₀, hc₀A, hc₀⟩ : ∃ c₀ ∈ A, ex * (x⁻¹ * c₀ * x) = c₀ := by
    by_cases hex1 : ex = 1
    · exact ⟨1, A.one_mem, by rw [hex1]; group⟩
    · refine ⟨x⁻¹ * ex * x, by simpa using conj_mem hxA hexA, ?_⟩
      rw [hσ ex hexA hex1, ← mul_assoc, mul_self_eq_one hset.elem hexA, one_mul]
  set x₀ := u * c₀ with hx₀
  have hfixx : x⁻¹ * x₀ * x = x₀ := by
    rw [hx₀, show x⁻¹ * (u * c₀) * x = (x⁻¹ * u * x) * (x⁻¹ * c₀ * x) by group, hxux,
      mul_assoc, hc₀]
  have hfixm : ∀ m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), m⁻¹ * a * m = a →
      m⁻¹ * x₀ * m = x₀ := by
    intro m hm hma
    have hmC : m ∈ Subgroup.centralizer (A : Set G) :=
      mem_centralizer_of_conj_eq hset h4 (hNA hm) ha ha1 (by
        calc m * a * m⁻¹ = m * (m⁻¹ * a * m) * m⁻¹ := by rw [hma]
          _ = a := by group)
    have hc := Subgroup.mem_centralizer_iff.mp hmC c₀ hc₀A
    calc m⁻¹ * x₀ * m = (m⁻¹ * u * m) * (m⁻¹ * (c₀ * m)) := by rw [hx₀]; group
      _ = u * (m⁻¹ * (m * c₀)) := by rw [hfixC m hm hmC, hc]
      _ = x₀ := by rw [hx₀]; group
  have hfixN : ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * x₀ * n = x₀ := by
    intro n hn
    have hnaA : n⁻¹ * a * n ∈ A := by simpa using conj_mem (Subgroup.inv_mem _ (hNA hn)) ha
    rcases mem_four hset.elem h4 ha hxaA hnaA ha1 (by simpa using conj_ne_one (n := x⁻¹) ha1)
      (Ne.symm hxa) with h | h | h | h
    · exact absurd h (by simpa using conj_ne_one (n := n⁻¹) ha1)
    · exact hfixm n hn h
    · have hm := hfixm (n * x⁻¹) (Subgroup.mul_mem _ hn (Subgroup.inv_mem _ hxS)) (by
        calc (n * x⁻¹)⁻¹ * a * (n * x⁻¹) = x * (n⁻¹ * a * n) * x⁻¹ := by group
          _ = a := by rw [h]; group)
      calc n⁻¹ * x₀ * n = x⁻¹ * ((n * x⁻¹)⁻¹ * x₀ * (n * x⁻¹)) * x := by group
        _ = x₀ := by rw [hm, hfixx]
    · have hσa := hσ a ha ha1
      have hm := hfixm (n * x⁻¹ * x⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn
        (Subgroup.inv_mem _ hxS)) (Subgroup.inv_mem _ hxS)) (by
        calc (n * x⁻¹ * x⁻¹)⁻¹ * a * (n * x⁻¹ * x⁻¹) = x * x * (n⁻¹ * a * n) * x⁻¹ * x⁻¹ := by
              simp only [mul_inv_rev, inv_inv, mul_assoc]
          _ = a := by rw [h, ← hσa]; group)
      have hfixx' : x⁻¹ * (x⁻¹ * x₀ * x) * x = x₀ := by rw [hfixx, hfixx]
      calc n⁻¹ * x₀ * n = x⁻¹ * (x⁻¹ * ((n * x⁻¹ * x⁻¹)⁻¹ * x₀ * (n * x⁻¹ * x⁻¹)) * x) * x := by
            group
        _ = x₀ := by rw [hm, hfixx']
  have hx₀S : x₀ ∈ (S : Subgroup G) := S.mul_mem huS (hset.le hc₀A)
  have hx₀2 : x₀ ^ 2 = 1 := by
    rw [hx₀, sq]
    calc u * c₀ * (u * c₀) = u * (c₀ * u) * c₀ := by group
      _ = u * (u * c₀) * c₀ := by rw [(Subgroup.mem_centralizer_iff.mp (hSA huS) c₀ hc₀A)]
      _ = (u * u) * (c₀ * c₀) := by group
      _ = 1 := by rw [huu, mul_self_eq_one hset.elem hc₀A, one_mul]
  have hx₀1 : x₀ ≠ 1 := fun h => huA (by
    have : u = c₀⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact A.inv_mem hc₀A)
  have hiso : ∀ g ∈ (⊤ : Subgroup G), g⁻¹ * x₀ * g ∈ (S : Subgroup G) → g⁻¹ * x₀ * g = x₀ := by
    intro g _ hg
    obtain ⟨n, hn, hng⟩ := exists_conj_normalizer_of_le (hcen x₀ hx₀S hx₀2)
      (hcen _ hg (by simpa using conj_sq_eq_one (g := g⁻¹) hx₀2))
    rw [← hng, hfixN n hn]
  have hZ : ∀ g : G, g * x₀ = x₀ * g := fun g => by
    have h := commutator_mem_oddCoreOf (fusionIsSylowIn_of_le (S := S) le_top) hx₀S
      (hcen x₀ hx₀S hx₀2) (by rw [← sq]; exact hx₀2) hx₀1 hiso (Subgroup.mem_top g)
    rw [oddCoreOf_top_eq_bot hset, Subgroup.mem_bot] at h
    calc g * x₀ = (g * x₀ * g⁻¹ * x₀⁻¹) * (x₀ * g) := by group
      _ = x₀ * g := by rw [h, one_mul]
  have hcen' : x₀ ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hZ
  have := hset.isSimpleGroup
  rw [PropHSetup.center_eq_bot hset.nonabelian, Subgroup.mem_bot] at hcen'
  exact hx₀1 hcen'

end CFSG.Goldschmidt.Sec8
