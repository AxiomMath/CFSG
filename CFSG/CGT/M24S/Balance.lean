module

public import CFSG.CGT.M24S.Defs
import CFSG.GroupTheory.ThompsonAxB
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.M24S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Holt.General
open scoped Pointwise

variable {G : Type} [Group G]

private theorem mul_comm_of_mem {T : Subgroup G} (hT : IsElemAbelian 2 T) {a b : G}
    (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hT ha hb

private theorem inv_eq_self_of_mem {T : Subgroup G} (hT : IsElemAbelian 2 T) {a : G}
    (ha : a ∈ T) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hT.2 a ha)

private theorem eq_one_of_sq_eq_one_of_odd {x : G} (h2 : x ^ 2 = 1) (hodd : Odd (orderOf x)) :
    x = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)

private theorem isPGroup_of_isElemAbelian {T : Subgroup G} (hT : IsElemAbelian 2 T) :
    IsPGroup 2 T := CFSG.Open.IsElemAbelian.isPGroup hT

private theorem isPGroup_zpowers_of_sq_eq_one {b : G} (hb : b ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers b) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨1, Subtype.ext ?_⟩
  change (b ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

private theorem oddCoreOf_le (B : Subgroup G) : oddCoreOf B ≤ B :=
  Subgroup.map_subtype_le _

private theorem conj_mem_oddCoreOf {B : Subgroup G} {b q : G} (hb : b ∈ B)
    (hq : q ∈ oddCoreOf B) : b * q * b⁻¹ ∈ oddCoreOf B := by
  obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
  exact ⟨_, (CFSG.pPrimeCore_normal (p := 2) (G := B)).conj_mem q₀ hq₀ ⟨b, hb⟩, rfl⟩

variable [Finite G]

private theorem odd_card_oddCoreOf (B : Subgroup G) : Odd (Nat.card (oddCoreOf B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCoreOf, Subgroup.card_map_of_injective B.subtype_injective]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := B))

private theorem odd_orderOf_of_mem_oddCoreOf {B : Subgroup G} {g : G} (hg : g ∈ oddCoreOf B) :
    Odd (orderOf g) :=
  (odd_card_oddCoreOf B).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hg)

private theorem commute_of_thompson_A_times_B {Q B : Subgroup G} {c : G} (hQ : IsPGroup 2 Q)
    (hB : IsPGroup 2 B) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hc : Odd (orderOf c))
    (hcB : ∀ b ∈ B, c * b = b * c)
    (hfix : ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → c * q = q * c) :
    ∀ q ∈ Q, c * q = q * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.zpowers c with hAdef
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hcQ
  let α : A →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ)
  let β : B →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hBQ)
  have hα : ∀ (a : A) (q : Q), ((α a q : Q) : G) = (a : G) * q * (a : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : B) (q : Q), ((β b q : Q) : G) = (b : G) * q * (b : G)⁻¹ := fun _ _ => rfl
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAdef, Nat.card_zpowers]
    exact Nat.odd_iff.mp hc |> fun h => by omega
  have hab : ∀ (a : A) (b : B), (a : G) * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hcB b hb) k).eq
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext q
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    calc (a : G) * ((b : G) * q * (b : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * b) * q * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * q * ((b : G) * a)⁻¹ := by rw [hab a b]
      _ = (b : G) * ((a : G) * q * (a : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, ha⟩ r hr
    have hrB : ∀ b ∈ B, (r : G) * b = b * r := by
      intro b hb
      have h := congrArg Subtype.val (hr ⟨b, hb⟩)
      rw [hβ] at h
      calc (r : G) * b = b * r * b⁻¹ * b := by rw [h]
        _ = b * r := by group
    have hcr := hfix r r.2 hrB
    apply Subtype.ext
    rw [hα]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have : Commute (c ^ k) (r : G) := Commute.zpow_left hcr k
    change c ^ k * r * (c ^ k)⁻¹ = r
    rw [this.eq]
    group
  have h := CFSG.GroupTheory.thompson_A_times_B hQ hA2 hB α β hcomm hfix'
  intro q hq
  have hq' := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : G))
    (h ⟨c, Subgroup.mem_zpowers c⟩)
  rw [hα] at hq'
  change c * q * c⁻¹ = ((1 : MulAut Q) ⟨q, hq⟩ : G) at hq'
  rw [MulAut.one_apply] at hq'
  calc c * q = c * q * c⁻¹ * c := by group
    _ = q * c := by rw [hq']

theorem four_le_card_inf_centralizer_of_sq_eq_one {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (hcard : Nat.card T = 16) {v : G} (hv : v ∈ Subgroup.normalizer (T : Set G))
    (hv2 : v ^ 2 = 1) : 4 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({v} : Set G)) := by
  have hvv : v * v = 1 := by rw [← sq]; exact hv2
  have hvT : ∀ t ∈ T, v * t * v ∈ T := fun t ht => by
    have := (Subgroup.mem_normalizer_iff.mp hv t).mp ht
    rwa [inv_eq_of_mul_eq_one_right hvv] at this
  let φ : T →* T :=
    { toFun := fun t => ⟨t * (v * t * v), T.mul_mem t.2 (hvT t t.2)⟩
      map_one' := Subtype.ext (by
        change (1 : G) * (v * 1 * v) = 1
        rw [one_mul, mul_one, hvv])
      map_mul' := fun s t => Subtype.ext (by
        change (s : G) * t * (v * (s * t) * v) = s * (v * s * v) * (t * (v * t * v))
        have hc := mul_comm_of_mem hT t.2 (hvT s s.2)
        have h1 : v * ((s : G) * t) * v = (v * s * v) * (v * t * v) := by
          calc v * ((s : G) * t) * v = v * s * (v * v) * t * v := by rw [hvv]; group
            _ = (v * s * v) * (v * t * v) := by group
        rw [h1]
        calc (s : G) * t * ((v * s * v) * (v * t * v))
            = s * (t * (v * s * v)) * (v * t * v) := by group
          _ = s * ((v * s * v) * t) * (v * t * v) := by rw [hc]
          _ = s * (v * s * v) * (t * (v * t * v)) := by group) }
  set F := T ⊓ Subgroup.centralizer ({v} : Set G) with hF
  have hmemF : ∀ t : T, v * (t : G) * v = t → (t : G) ∈ F := fun t ht => by
    refine Subgroup.mem_inf.mpr ⟨t.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (t : G) * v = (v * t * v) * v := by rw [ht]
      _ = v * t * (v * v) := by group
      _ = v * t := by rw [hvv, mul_one]
  have hker : φ.ker ≤ F.subgroupOf T := fun t ht => by
    have h1 : (t : G) * (v * t * v) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_self_of_mem hT t.2]
  have hrange : φ.range ≤ F.subgroupOf T := by
    rintro _ ⟨t, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    change v * ((t : G) * (v * t * v)) * v = t * (v * t * v)
    have hc := mul_comm_of_mem hT t.2 (hvT t t.2)
    calc v * ((t : G) * (v * t * v)) * v = v * ((v * t * v) * t) * v := by rw [hc]
      _ = (v * v) * t * v * t * v := by group
      _ = t * v * t * v := by rw [hvv, one_mul]
      _ = t * (v * t * v) := by group
  have hcardF : Nat.card (F.subgroupOf T) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h16 : 16 ≤ Nat.card F * Nat.card F := by
    rw [← hcardF, ← hcard, ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
    exact Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)
  by_contra hlt
  have h3 : Nat.card F ≤ 3 := by omega
  have := Nat.mul_le_mul h3 h3
  omega

variable {T H : Subgroup G}

private theorem mem_oddCore_of_odd (hT : IsElemAbelian 2 T) (hL : LocalFacts T H) {c : G}
    (hc : c ∈ Subgroup.centralizer (T : Set G)) (hodd : Odd (orderOf c)) :
    c ∈ oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  have hCT := hL.centralizer_T_eq
  set C := Subgroup.centralizer (T : Set G) with hC
  set K := oddCoreOf C with hK
  have hTC : T ≤ C := fun t ht => Subgroup.mem_centralizer_iff.mpr fun s hs =>
    mul_comm_of_mem hT hs ht
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => conj_mem_oddCoreOf (hTC ht) hk,
      fun hk => by simpa [mul_assoc] using conj_mem_oddCoreOf (C.inv_mem (hTC ht)) hk⟩
  have hcTK : c ∈ (T : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T K hTK, ← hCT]
    exact hc
  obtain ⟨t, ht, k, hk, rfl⟩ := Set.mem_mul.mp hcTK
  have htk : Commute t k := Subgroup.mem_centralizer_iff.mp (oddCoreOf_le C hk) t ht
  obtain ⟨j, hj⟩ := hodd
  have h1 : t ^ orderOf (t * k) * k ^ orderOf (t * k) = 1 := by
    rw [← htk.mul_pow, pow_orderOf_eq_one]
  have htm : t ^ orderOf (t * k) = t := by
    rw [hj, pow_succ, pow_mul, hT.2 t ht, one_pow, one_mul]
  have htK : t ∈ K := by
    rw [← htm, eq_inv_of_mul_eq_one_left h1]
    exact K.inv_mem (K.pow_mem hk _)
  rw [eq_one_of_sq_eq_one_of_odd (hT.2 t ht) (odd_orderOf_of_mem_oddCoreOf htK), one_mul]
  exact hk

theorem le_oddCore_of_balance (h : Hyp T H) (hL : LocalFacts T H) {b : G}
    (hb : b ∈ Subgroup.normalizer (T : Set G)) (hb2 : b ^ 2 = 1) {W : Subgroup G}
    (hW : Odd (Nat.card W)) (hWT : W ≤ Subgroup.normalizer (T : Set G))
    (hWb : W ≤ Subgroup.centralizer ({b} : Set G))
    (hnorm : ∀ t ∈ T, t * b = b * t → ∀ w ∈ W, t * w * t⁻¹ ∈ W) :
    W ≤ oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  have hT := h.wc.1
  intro c hc
  have hcodd : Odd (orderOf c) := hW.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hc)
  refine mem_oddCore_of_odd hT hL (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_) hcodd
  have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp (hWb hc)
  refine (commute_of_thompson_A_times_B (B := Subgroup.zpowers b) (isPGroup_of_isElemAbelian hT)
    (isPGroup_zpowers_of_sq_eq_one hb2) (hWT hc) (Subgroup.zpowers_le.mpr hb) hcodd
    (fun x hx => ?_) (fun q hq hqB => ?_) t ht).symm
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right hcb k).eq
  · have hqb : q * b = b * q := hqB b (Subgroup.mem_zpowers b)
    have hdT : c * q * c⁻¹ * q⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWT hc) q).mp hq) (T.inv_mem hq)
    have hdW : c * q * c⁻¹ * q⁻¹ ∈ W := by
      simpa [mul_assoc] using W.mul_mem hc (hnorm q hq hqb c⁻¹ (W.inv_mem hc))
    have hd := eq_one_of_sq_eq_one_of_odd (hT.2 _ hdT)
      (hW.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hdW))
    calc c * q = c * q * c⁻¹ * q⁻¹ * q * c := by group
      _ = q * c := by rw [hd, one_mul]

omit [Finite G] in
private theorem mem_normalizer_oddCore_of_commute (hL : LocalFacts T H) {y u : G} (hy : y ∈ T)
    (hy1 : y ≠ 1) (hu : u * y = y * u) :
    u ∈ Subgroup.normalizer (oddCoreOf (Subgroup.centralizer (T : Set G)) : Set G) := by
  have huC : u ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hu
  rw [← hL.oddCore_eq y hy hy1]
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => conj_mem_oddCoreOf huC hk,
    fun hk => ?_⟩
  simpa [mul_assoc] using conj_mem_oddCoreOf (Subgroup.inv_mem _ huC) hk

theorem conjSubgroup_oddCore_eq_of_commute (h : Hyp T H) (hL : LocalFacts T H) {g x y : G}
    (hx : x ∈ T) (hx1 : x ≠ 1) (hy : y ∈ T) (hy1 : y ≠ 1)
    (hxy : x * (g * y * g⁻¹) = g * y * g⁻¹ * x) :
    conjSubgroup g (oddCoreOf (Subgroup.centralizer (T : Set G))) =
      oddCoreOf (Subgroup.centralizer (T : Set G)) := by
  have hT := h.wc.1
  set K := oddCoreOf (Subgroup.centralizer (T : Set G)) with hK
  set y' := g * y * g⁻¹ with hy'
  have hy'N : y' ∈ Subgroup.normalizer (T : Set G) :=
    hL.centralizer_le x hx hx1 (Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm)
  have hy'2 : y' ^ 2 = 1 := by rw [hy', conj_pow, hT.2 y hy, mul_one, mul_inv_cancel]
  have hmemKg : ∀ k, k ∈ conjSubgroup g K ↔ g⁻¹ * k * g ∈ K := fun k => mem_conjSubgroup
  have hKgy : conjSubgroup g K ≤ Subgroup.centralizer ({y'} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (g⁻¹ * k * g) * y = y * (g⁻¹ * k * g) :=
      (Subgroup.mem_centralizer_iff.mp (oddCoreOf_le _ ((hmemKg k).mp hk)) y hy).symm
    calc k * y' = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by rw [hy']; group
      _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
      _ = y' * k := by rw [hy']; group
  have hNKg : ∀ u, u * y' = y' * u → u ∈ Subgroup.normalizer (conjSubgroup g K : Set G) := by
    intro u hu
    have hu' : (g⁻¹ * u * g) * y = y * (g⁻¹ * u * g) := by
      calc (g⁻¹ * u * g) * y = g⁻¹ * (u * y') * g := by rw [hy']; group
        _ = g⁻¹ * (y' * u) * g := by rw [hu]
        _ = y * (g⁻¹ * u * g) := by rw [hy']; group
    have hn := Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_commute hL hy hy1 hu')
    refine Subgroup.mem_normalizer_iff.mpr fun k => ?_
    have he : (g⁻¹ * u * g) * (g⁻¹ * k * g) * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * k * u⁻¹) * g := by
      group
    rw [hmemKg, hmemKg, hn (g⁻¹ * k * g), he]
  set F := T ⊓ Subgroup.centralizer ({y'} : Set G) with hF
  have hFab : IsElemAbelian 2 F :=
    ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_mem hT (Subgroup.mem_inf.mp a.2).1
      (Subgroup.mem_inf.mp b.2).1)⟩⟩, fun a ha => hT.2 a (Subgroup.mem_inf.mp ha).1⟩
  have hF4 : 2 ^ 2 ≤ Nat.card F := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact four_le_card_inf_centralizer_of_sq_eq_one hT hL.card_T hy'N hy'2
  have hFN : F ≤ Subgroup.normalizer (conjSubgroup g K : Set G) := fun f hf =>
    hNKg f (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hf).2)
  have hcardKg : Nat.card (conjSubgroup g K) = Nat.card K := by
    rw [conjSubgroup]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKgodd : Odd (Nat.card (conjSubgroup g K)) := hcardKg ▸ odd_card_oddCoreOf _
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hFab hF4 hFN (Nat.coprime_two_left.mpr hKgodd)
  have hle : conjSubgroup g K ≤ K := by
    rw [← hgen]
    refine iSup_le fun f => iSup_le fun hf => iSup_le fun hf1 => ?_
    have hfT := (Subgroup.mem_inf.mp hf).1
    refine le_oddCore_of_balance h hL hy'N hy'2 ?_ ?_ ?_ ?_
    · exact hKgodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    · exact inf_le_right.trans (hL.centralizer_le f hfT hf1)
    · exact inf_le_left.trans hKgy
    · intro t ht hty w hw
      have htf : t ∈ Subgroup.centralizer ({f} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_mem hT ht hfT)
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hNKg t hty) w).mp
        (Subgroup.mem_inf.mp hw).1, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htf (Subgroup.mem_inf.mp hw).2)
        (Subgroup.inv_mem _ htf)
  exact Subgroup.eq_of_le_of_card_ge hle hcardKg.ge

end CFSG.CGT.M24S
