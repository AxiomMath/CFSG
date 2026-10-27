module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterStep
public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicSylow

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

section Config

variable {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X}

theorem Chev204Hyp.not_le_centralizer (hH : Chev204Hyp p K B) :
    ¬ B ≤ Subgroup.centralizer (K : Set X) := by
  intro hBC
  obtain ⟨y, hyo, hyZ⟩ := exists_orderOf_eq_prime_not_mem_center hH.quasi hH.prime hH.odd hH.dvd
  have hyc : (y : X) ∈ Subgroup.centralizer (B : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hBC hb) (y : X) y.2).symm
  have hyo' : orderOf (y : X) = p := by rw [Subgroup.orderOf_coe]; exact hyo
  have hyB : (y : X) ∈ B := mem_of_mem_centralizer_orderOf_eq_prime hH.scp hyc hyo'
  apply hyZ
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hBC hyB) g g.2)

theorem Chev204Hyp.autOrderIn_eq (hH : Chev204Hyp p K B) (hcyc : autOrderIn B K ≤ p) :
    autOrderIn B K = p := by
  obtain ⟨r, hr⟩ := exists_pow_autOrderIn hH.prime hH.elem hH.norm
  have hne : autOrderIn B K ≠ 1 := by
    intro h1
    apply hH.not_le_centralizer
    unfold autOrderIn at h1
    rw [inf_of_le_left hH.norm] at h1
    exact (Subgroup.relIndex_eq_one.1 h1)
  rcases Nat.lt_or_ge r 2 with h | h
  · interval_cases r
    · exact absurd (by simpa using hr) hne
    · simpa using hr
  · exfalso
    have h1 : p ^ 2 ≤ autOrderIn B K := by
      rw [hr]; exact Nat.pow_le_pow_right hH.prime.pos h
    have h2 : p ^ 2 ≤ p := h1.trans hcyc
    nlinarith [hH.prime.two_le]

theorem exists_pow_inv_mul_mem_centralizer (hp : p.Prime) (hel : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hcard : autOrderIn B K = p) {b₁ : X} (hb₁ : b₁ ∈ B)
    (hb₁C : b₁ ∉ Subgroup.centralizer (K : Set X)) {b : X} (hb : b ∈ B) :
    ∃ j : ℕ, (b₁ ^ j)⁻¹ * b ∈ Subgroup.centralizer (K : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hC
  set N₀ : Subgroup ↥B := C.subgroupOf B with hN₀
  haveI := hel.1
  haveI : N₀.Normal := Subgroup.normal_of_comm N₀
  have hidx : N₀.index = p := by
    have := hcard
    unfold autOrderIn at this
    rw [inf_of_le_left hBN] at this
    exact this
  have hQ : Nat.card (↥B ⧸ N₀) = p := by rw [← Subgroup.index, hidx]
  set q₁ : ↥B ⧸ N₀ := QuotientGroup.mk (⟨b₁, hb₁⟩ : ↥B) with hq₁
  have hq₁ne : q₁ ≠ 1 := by
    intro h
    apply hb₁C
    have := (QuotientGroup.eq_one_iff _).1 h
    exact (Subgroup.mem_subgroupOf.1 this)
  obtain ⟨j, hj⟩ := mem_powers_of_prime_card hQ hq₁ne (g' := (QuotientGroup.mk (⟨b, hb⟩ : ↥B) : ↥B ⧸ N₀))
  refine ⟨j, ?_⟩
  have h1 : (QuotientGroup.mk ((⟨b₁, hb₁⟩ : ↥B) ^ j) : ↥B ⧸ N₀) = QuotientGroup.mk ⟨b, hb⟩ := by
    rw [QuotientGroup.mk_pow]; exact hj
  have h2 := QuotientGroup.eq.1 h1
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa using h3

theorem mem_center_of_mem_centralizer {y : ↥K} (h : (y : X) ∈ Subgroup.centralizer (K : Set X)) :
    y ∈ Subgroup.center ↥K := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h g g.2)

theorem mem_centralizer_of_mem_center {y : ↥K} (h : y ∈ Subgroup.center ↥K) :
    (y : X) ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 h ⟨g, hg⟩))

theorem normalizerMonoidHom_pow_eq_one {b : X} (hbN : b ∈ Subgroup.normalizer (K : Set X))
    {n : ℕ} (hb : b ^ n = 1) : (K.normalizerMonoidHom ⟨b, hbN⟩) ^ n = 1 := by
  rw [← map_pow]
  have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ n = 1 :=
    Subtype.ext (by simpa using hb)
  rw [this, map_one]

theorem Chev204Hyp.inducesInnerIn_of_cyclic (hK65 : KD65 p) (hH : Chev204Hyp p K B)
    (hcyc : autOrderIn B K ≤ p) : InducesInnerIn B K := by
  classical
  have hp := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard := hH.autOrderIn_eq hcyc
  intro b hbBN
  have hbB : b ∈ B := hbBN.1
  by_contra hout
  push Not at hout
  have hbC : b ∉ Subgroup.centralizer (K : Set X) := fun h => hout 1 K.one_mem (by simpa using h)
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_outer hK65 hH hbB (fun ⟨k, hk, hc⟩ => hout k hk hc)
  have hbN : b ∈ Subgroup.normalizer (K : Set X) := hH.norm hbB
  have hbp : b ^ p = 1 := hH.elem.2 b hbB
  have hσ := normalizerMonoidHom_pow_eq_one (K := K) hbN hbp
  obtain ⟨y, hyo, hyfix⟩ := exists_fixed_orderOf_eq_prime (K.normalizerMonoidHom ⟨b, hbN⟩) hσ hH.dvd
  have hbyc : b * (y : X) = (y : X) * b := by
    have h1 : b * (y : X) * b⁻¹ = (y : X) := congrArg Subtype.val hyfix
    calc b * (y : X) = (b * (y : X) * b⁻¹) * b := by group
      _ = (y : X) * b := by rw [h1]
  have hyB : (y : X) ∈ B := by
    have hyC : (y : X) ∈ Subgroup.centralizer (B : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      obtain ⟨j, hj⟩ := exists_pow_inv_mul_mem_centralizer hp hH.elem hH.norm hcard hbB hbC hb'
      set c := (b ^ j)⁻¹ * b' with hcdef
      have hb'c : b' = b ^ j * c := by rw [hcdef]; group
      have h1 : (y : X) * b ^ j = b ^ j * (y : X) :=
        (Commute.pow_right (show Commute (y : X) b from hbyc.symm) j).eq
      have h2 : (y : X) * c = c * (y : X) := Subgroup.mem_centralizer_iff.1 hj (y : X) y.2
      calc b' * (y : X) = b ^ j * (c * (y : X)) := by rw [hb'c]; group
        _ = b ^ j * ((y : X) * c) := by rw [h2]
        _ = (b ^ j * (y : X)) * c := by group
        _ = ((y : X) * b ^ j) * c := by rw [h1]
        _ = (y : X) * (b ^ j * c) := by group
        _ = (y : X) * b' := by rw [hb'c]
    have hyo' : orderOf (y : X) = p := by rw [Subgroup.orderOf_coe]; exact hyo
    exact mem_of_mem_centralizer_orderOf_eq_prime hH.scp hyC hyo'
  have hyC : (y : X) ∉ Subgroup.centralizer (K : Set X) := by
    intro h
    have := mem_center_of_mem_centralizer h
    rw [hZ, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hyo
    exact hp.one_lt.ne hyo
  obtain ⟨j, hj⟩ := exists_pow_inv_mul_mem_centralizer hp hH.elem hH.norm hcard hyB hyC hbB
  exact hout ((y : X) ^ j) (K.pow_mem y.2 j) hj

theorem Chev204Hyp.exists_gen (hH : Chev204Hyp p K B) (hcyc : autOrderIn B K ≤ p)
    (hin : InducesInnerIn B K) :
    ∃ (k : ↥K) (b₀ : X), b₀ ∈ B ∧ (∀ x ∈ K, b₀ * x * b₀⁻¹ = (k : X) * x * (k : X)⁻¹) ∧
      k ∉ Subgroup.center ↥K ∧ k ^ p ∈ Subgroup.center ↥K ∧
      ∀ x : ↥K, x ^ p = 1 → x * k = k * x → x ∈ Subgroup.zpowers k ⊔ Subgroup.center ↥K := by
  classical
  have hp := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard := hH.autOrderIn_eq hcyc
  obtain ⟨b₀, hb₀B, hb₀C⟩ : ∃ b ∈ B, b ∉ Subgroup.centralizer (K : Set X) := by
    by_contra h
    push Not at h
    exact hH.not_le_centralizer (fun b hb => h b hb)
  have hb₀N : b₀ ∈ Subgroup.normalizer (K : Set X) := hH.norm hb₀B
  obtain ⟨k₀, hk₀K, hk₀c⟩ := hin b₀ ⟨hb₀B, hb₀N⟩
  set c₀ : X := k₀⁻¹ * b₀ with hc₀
  have hb₀ : b₀ = k₀ * c₀ := by rw [hc₀]; group
  have hk₀C : k₀ ∉ Subgroup.centralizer (K : Set X) := by
    intro h
    apply hb₀C
    rw [hb₀]
    exact Subgroup.mul_mem _ h hk₀c
  have hcomm : k₀ * c₀ = c₀ * k₀ := Subgroup.mem_centralizer_iff.1 hk₀c k₀ hk₀K
  set k : ↥K := ⟨k₀, hk₀K⟩ with hkdef
  refine ⟨k, b₀, hb₀B, ?_, fun h => hk₀C (mem_centralizer_of_mem_center h), ?_, ?_⟩
  · intro x hx
    have h1 : x * c₀ = c₀ * x := Subgroup.mem_centralizer_iff.1 hk₀c x hx
    calc b₀ * x * b₀⁻¹ = k₀ * (c₀ * x * c₀⁻¹) * k₀⁻¹ := by rw [hb₀]; group
      _ = k₀ * (x * c₀ * c₀⁻¹) * k₀⁻¹ := by rw [h1]
      _ = k₀ * x * k₀⁻¹ := by group
  ·
    apply mem_center_of_mem_centralizer
    have hb₀p : b₀ ^ p = 1 := hH.elem.2 b₀ hb₀B
    have h1 : k₀ ^ p * c₀ ^ p = 1 := by
      rw [← Commute.mul_pow hcomm, ← hb₀, hb₀p]
    have h2 : k₀ ^ p = (c₀ ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
    show k₀ ^ p ∈ _
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hk₀c p)
  · intro x hxp hxk
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    have hx'o : orderOf (x : X) = p := by rw [Subgroup.orderOf_coe]; exact hxo
    have hxb₀ : (x : X) * b₀ = b₀ * (x : X) := by
      have h1 : (x : X) * k₀ = k₀ * (x : X) := congrArg Subtype.val hxk
      have h2 : (x : X) * c₀ = c₀ * (x : X) := Subgroup.mem_centralizer_iff.1 hk₀c (x : X) x.2
      calc (x : X) * b₀ = (x : X) * (k₀ * c₀) := by rw [← hb₀]
        _ = ((x : X) * k₀) * c₀ := by group
        _ = (k₀ * (x : X)) * c₀ := by rw [h1]
        _ = k₀ * ((x : X) * c₀) := by group
        _ = k₀ * (c₀ * (x : X)) := by rw [h2]
        _ = (k₀ * c₀) * (x : X) := by group
        _ = b₀ * (x : X) := by rw [← hb₀]
    have hxB' : (x : X) ∈ Subgroup.centralizer (B : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨j, hj⟩ := exists_pow_inv_mul_mem_centralizer hp hH.elem hH.norm hcard hb₀B hb₀C hb
      set c := (b₀ ^ j)⁻¹ * b with hcdef
      have hbc : b = b₀ ^ j * c := by rw [hcdef]; group
      have h1 : (x : X) * b₀ ^ j = b₀ ^ j * (x : X) :=
        (Commute.pow_right (show Commute (x : X) b₀ from hxb₀) j).eq
      have h2 : (x : X) * c = c * (x : X) := Subgroup.mem_centralizer_iff.1 hj (x : X) x.2
      calc b * (x : X) = b₀ ^ j * (c * (x : X)) := by rw [hbc]; group
        _ = b₀ ^ j * ((x : X) * c) := by rw [h2]
        _ = (b₀ ^ j * (x : X)) * c := by group
        _ = ((x : X) * b₀ ^ j) * c := by rw [h1]
        _ = (x : X) * (b₀ ^ j * c) := by group
        _ = (x : X) * b := by rw [hbc]
    have hxB : (x : X) ∈ B := mem_of_mem_centralizer_orderOf_eq_prime hH.scp hxB' hx'o
    obtain ⟨j, hj⟩ := exists_pow_inv_mul_mem_centralizer hp hH.elem hH.norm hcard hb₀B hb₀C hxB
    have hb₀j : b₀ ^ j = k₀ ^ j * c₀ ^ j := by
      rw [hb₀]; exact Commute.mul_pow hcomm j
    have hc₀j : c₀ ^ j ∈ Subgroup.centralizer (K : Set X) := Subgroup.pow_mem _ hk₀c j
    have hmem : (k₀ ^ j)⁻¹ * (x : X) ∈ Subgroup.centralizer (K : Set X) := by
      have : (k₀ ^ j)⁻¹ * (x : X) = c₀ ^ j * ((b₀ ^ j)⁻¹ * (x : X)) := by
        rw [hb₀j]; group
      rw [this]
      exact Subgroup.mul_mem _ hc₀j hj
    have hz : (k ^ j)⁻¹ * x ∈ Subgroup.center ↥K := by
      apply mem_center_of_mem_centralizer
      simpa [hkdef] using hmem
    have hxe : x = k ^ j * ((k ^ j)⁻¹ * x) := by group
    rw [hxe]
    exact Subgroup.mul_mem_sup ((Subgroup.zpowers k).pow_mem (Subgroup.mem_zpowers k) j) hz

end Config

end CFSG.HardMathSupport.Dickson.I271
