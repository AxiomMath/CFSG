module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift4
public import CFSG.LargeExtraspecial.BridgeNat
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB

section Elementary

variable {G : Type} [Group G]

theorem isElemAbelian_zpowers' {p : ℕ} {a : G} (ha : a ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers a) := by
  refine ⟨inferInstance, fun g hg => ?_⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem centralizer_zpowers_sup (a b : G) :
    Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) =
      cx a ⊓ cx b := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Set.union_def]
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (h a (Or.inl (Subgroup.mem_zpowers a))).symm,
      Subgroup.mem_centralizer_singleton_iff.2 (h b (Or.inr (Subgroup.mem_zpowers b))).symm⟩
  · rintro ⟨ha, hb⟩ h (hh | hh)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute a g from
        (Subgroup.mem_centralizer_singleton_iff.1 ha).symm) i).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute b g from
        (Subgroup.mem_centralizer_singleton_iff.1 hb).symm) i).eq

variable [Finite G]

private theorem inf_zpowers_eq_bot {p : ℕ} (hp : p.Prime) {x : G} (hx : orderOf x = p)
    {B : Subgroup G} (hxB : x ∉ B) : Subgroup.zpowers x ⊓ B = ⊥ := by
  have hdvd : Nat.card (Subgroup.zpowers x ⊓ B : Subgroup G) ∣ p := by
    rw [← hx, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h | h
  · exact Subgroup.card_eq_one.1 h
  · exfalso
    apply hxB
    have heq : Subgroup.zpowers x ⊓ B = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hx, h])
    have : x ∈ Subgroup.zpowers x ⊓ B := by rw [heq]; exact Subgroup.mem_zpowers x
    exact this.2

theorem card_zpowers_sup {p : ℕ} (hp : p.Prime) {x : G} (hx : orderOf x = p) {B : Subgroup G}
    (hxB : x ∉ B) (hBx : B ≤ cx x) :
    Nat.card (Subgroup.zpowers x ⊔ B : Subgroup G) = p * Nat.card B := by
  have hBN : B ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := fun b hb =>
    CatB.mem_normalizer_zpowers_of_commute
      (show Commute b x from Subgroup.mem_centralizer_singleton_iff.1 (hBx hb))
  have h := card_sup_mul_card_inf_of_le_normalizer hBN
  rw [inf_zpowers_eq_bot hp hx hxB, Subgroup.card_bot, mul_one, Nat.card_zpowers, hx] at h
  exact h

end Elementary

section Images

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_map_subtype' {L : Subgroup G} (A : Subgroup ↥L) :
    (A.map L.subtype).subgroupOf L = A :=
  Subgroup.comap_map_eq_self_of_injective L.subtype_injective A

theorem lImg_map_subtype (p : ℕ) {L : Subgroup G} (A : Subgroup ↥L) :
    lImg p L (A.map L.subtype) = A.map (pQuotHom p L) := by
  unfold lImg
  rw [subgroupOf_map_subtype']

theorem lImg_sup (p : ℕ) {L A B : Subgroup G} (hA : A ≤ L) (hB : B ≤ L) :
    lImg p L (A ⊔ B) = lImg p L A ⊔ lImg p L B := by
  unfold lImg
  rw [← Subgroup.map_sup]
  congr 1
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le (sup_le hA hB)]

theorem centralizer_subgroupOf' {L S : Subgroup G} (hS : S ≤ L) :
    (Subgroup.centralizer (S : Set G)).subgroupOf L =
      Subgroup.centralizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    exact Subtype.ext (h s hs)
  · intro h s hs
    exact congrArg Subtype.val (h ⟨s, hS hs⟩ hs)

theorem exists_eq_zpowers_of_card_two {H : Type} [Group H] [Finite H] {Z : Subgroup H}
    (hZ : Nat.card Z = 2) : ∃ z ∈ Z, Z = Subgroup.zpowers z ∧ z ^ 2 = 1 := by
  have hne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨z, hz⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hz2 : z ^ 2 = 1 := by
    have h1 := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ] at h1
    simpa using congrArg Subtype.val h1
  refine ⟨z, hz, ?_, hz2⟩
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz)
    (by rw [Nat.card_zpowers, hord, hZ])).symm

theorem map_inf_centralizer_eq {H M : Type} [Group H] [Finite H] [Group M] {q : ℕ}
    (hq : q.Prime) (π : H →* M) (hkq : ¬ q ∣ Nat.card π.ker) {A : Subgroup H} {y : H}
    (hyA : y ∈ A) (hy : IsPGroup q (Subgroup.zpowers y)) :
    (A ⊓ Subgroup.centralizer ({y} : Set H)).map π =
      A.map π ⊓ Subgroup.centralizer ({π y} : Set M) := by
  apply le_antisymm
  · intro m hm
    obtain ⟨a, ha, rfl⟩ := hm
    have haA : a ∈ A := ha.1
    have hay : a ∈ Subgroup.centralizer ({y} : Set H) := ha.2
    refine ⟨⟨a, haA, rfl⟩, ?_⟩
    show π a ∈ Subgroup.centralizer ({π y} : Set M)
    rw [Subgroup.mem_centralizer_singleton_iff] at hay ⊢
    rw [← map_mul, ← map_mul, hay]
  · intro m hm
    have hmA : m ∈ A.map π := hm.1
    have hmy : m ∈ Subgroup.centralizer ({π y} : Set M) := hm.2
    obtain ⟨a, haA, rfl⟩ := hmA
    rw [Subgroup.mem_centralizer_singleton_iff] at hmy
    set ψ : ↥A →* M := π.comp A.subtype with hψ
    have hkψ : ¬ q ∣ Nat.card ψ.ker := fun h => hkq (h.trans (CatB.card_ker_comp_subtype_dvd π A))
    have hyψ : IsPGroup q (Subgroup.zpowers (⟨y, hyA⟩ : ↥A)) := isPGroup_zpowers_mk hyA hy
    obtain ⟨n, hn, hkn⟩ := exists_mem_ker_mul_commute hq ψ hkψ hyψ (k := ⟨a, haA⟩) hmy
    refine ⟨((⟨a, haA⟩ : ↥A) * n : ↥A), ⟨((⟨a, haA⟩ : ↥A) * n).2, ?_⟩, ?_⟩
    · show (((⟨a, haA⟩ : ↥A) * n : ↥A) : H) ∈ Subgroup.centralizer ({y} : Set H)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hkn
    · have hn' : π (n : H) = 1 := hn
      show π ((a : H) * (n : H)) = π a
      rw [map_mul, hn', mul_one]

end Images

section Extraspecial

theorem isExtraSpec2_congr {G₁ G₂ : Type} [Group G₁] [Group G₂] {A : Subgroup G₁}
    {B : Subgroup G₂} (e : A ≃* B) : IsExtraSpec2 A ↔ IsExtraSpec2 B :=
  CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_congr e

end Extraspecial

section Six

variable {H M : Type} [Group H] [Finite H] [Group M]

theorem map_inf_centralizer_self (π : H →* M) {S : Subgroup H}
    (hSinj : Function.Injective (π.comp S.subtype)) :
    (S ⊓ Subgroup.centralizer (S : Set H)).map π =
      S.map π ⊓ Subgroup.centralizer ((S.map π : Subgroup M) : Set M) := by
  apply le_antisymm
  · intro m hm
    obtain ⟨s, hs, rfl⟩ := hm
    have hsS : s ∈ S := hs.1
    have hsC : s ∈ Subgroup.centralizer (S : Set H) := hs.2
    refine ⟨⟨s, hsS, rfl⟩, ?_⟩
    show π s ∈ Subgroup.centralizer ((S.map π : Subgroup M) : Set M)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hsC t ht]
  · intro m hm
    have hmS : m ∈ S.map π := hm.1
    have hmC : m ∈ Subgroup.centralizer ((S.map π : Subgroup M) : Set M) := hm.2
    obtain ⟨s, hsS, rfl⟩ := hmS
    refine ⟨s, ⟨hsS, ?_⟩, rfl⟩
    show s ∈ Subgroup.centralizer (S : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 : π t * π s = π s * π t := Subgroup.mem_centralizer_iff.1 hmC (π t) ⟨t, ht, rfl⟩
    have h2 : (⟨t * s, S.mul_mem ht hsS⟩ : S) = ⟨s * t, S.mul_mem hsS ht⟩ :=
      hSinj (by simpa using h1)
    exact congrArg Subtype.val h2

theorem le_centralizer_of_map_le (π : H →* M) (hk2 : ¬ 2 ∣ Nat.card π.ker) {S F : Subgroup H}
    (hS : IsPGroup 2 S) (hSinj : Function.Injective (π.comp S.subtype)) {z : H} (hzS : z ∈ S)
    (hFS : F ≤ Subgroup.normalizer (S : Set H)) (hzF : z ∈ Subgroup.normalizer (F : Set H))
    (hFz : F.map π ≤ Subgroup.centralizer ({π z} : Set M)) :
    F ≤ Subgroup.centralizer ({z} : Set H) := by
  have hN0 : ∀ n ∈ F, π n = 1 → z * n = n * z := by
    intro n hn hn1
    have hcS : n * z * n⁻¹ * z⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.1 (hFS hn) z).1 hzS) (S.inv_mem hzS)
    have hck : π (n * z * n⁻¹ * z⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hn1]
      group
    have h1 : (⟨n * z * n⁻¹ * z⁻¹, hcS⟩ : S) = 1 := hSinj (by simpa using hck)
    have h2 : n * z * n⁻¹ * z⁻¹ = 1 := congrArg Subtype.val h1
    calc z * n = (n * z * n⁻¹ * z⁻¹)⁻¹ * (n * z) := by group
      _ = n * z := by rw [h2, inv_one, one_mul]
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  set m : H := k⁻¹ * (z * k * z⁻¹) with hm
  have hmF : m ∈ F := F.mul_mem (F.inv_mem hk) ((Subgroup.mem_normalizer_iff.1 hzF k).1 hk)
  have hm1 : π m = 1 := by
    have h1 : π k * π z = π z * π k :=
      Subgroup.mem_centralizer_singleton_iff.1 (hFz ⟨k, hk, rfl⟩)
    rw [hm, map_mul, map_inv, map_mul, map_mul, map_inv, ← h1]
    group
  have hzm : z * m = m * z := hN0 m hmF hm1
  have hzk : z * k * z⁻¹ = k * m := by rw [hm]; group
  have hzmj : ∀ j : ℕ, z * m ^ j * z⁻¹ = m ^ j := fun j => by
    rw [(Commute.pow_right (show Commute z m from hzm) j).eq, mul_inv_cancel_right]
  have key : ∀ j : ℕ, z ^ j * k * (z ^ j)⁻¹ = k * m ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc z ^ (j + 1) * k * (z ^ (j + 1))⁻¹ = z * (z ^ j * k * (z ^ j)⁻¹) * z⁻¹ := by group
        _ = (z * k * z⁻¹) * (z * m ^ j * z⁻¹) := by rw [ih]; group
        _ = k * m ^ (j + 1) := by rw [hzk, hzmj, pow_succ']; group
  obtain ⟨a, ha⟩ := hS ⟨z, hzS⟩
  have hza : z ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have h1 := key (2 ^ a)
  rw [hza, one_mul, inv_one, mul_one] at h1
  have hma : m ^ (2 ^ a) = 1 := by
    have := congrArg (fun y => k⁻¹ * y) h1
    simpa using this.symm
  have hodd : Odd (Nat.card π.ker) := Nat.odd_iff.2 (by omega)
  have hm' : m = 1 := eq_one_of_two_pow_of_odd hodd (k := a) (by exact hm1) hma
  have : z * k * z⁻¹ = k := by rw [hzk, hm', mul_one]
  calc k * z = z * k * z⁻¹ * z := by rw [this]
    _ = z * k := by group

theorem le_glaPLayer_of_map_le {p : ℕ} (hp : p.Prime) (π : H →* M)
    (hkp : ¬ p ∣ Nat.card π.ker) {F Y : Subgroup H} (hF : S10.PPrimePerfect p F) (hFY : F ≤ Y)
    (hmap : F.map π ≤ (GLAPLayer p Y).map π) : F ≤ GLAPLayer p Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEY : GLAPLayer p Y ≤ Y := glaPLayer_le_self' Y
  have hYE : Y ≤ Subgroup.normalizer (GLAPLayer p Y : Set H) :=
    HardMathSupport.Solomon.UniquenessMaximal.Sec7.le_normalizer_glaPLayer p Y
  have hEΘ : GLAPLayer p Y ≤ Subgroup.normalizer ((Y ⊓ π.ker : Subgroup H) : Set H) := by
    intro e he
    refine S10.mem_normalizer_inf_of (Subgroup.le_normalizer (hEY he)) ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker π)]
    exact Subgroup.mem_top _
  have hΘ : Nat.Coprime (Nat.card (Y ⊓ π.ker : Subgroup H)) p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right)
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hkp))
  have hle : F ≤ GLAPLayer p Y ⊔ (Y ⊓ π.ker) := by
    intro f hf
    obtain ⟨e, he, hef⟩ := hmap ⟨f, hf, rfl⟩
    have hk : e⁻¹ * f ∈ Y ⊓ π.ker := ⟨Y.mul_mem (Y.inv_mem (hEY he)) (hFY hf), by
      show e⁻¹ * f ∈ π.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hef, inv_mul_cancel]⟩
    rw [show f = e * (e⁻¹ * f) by group]
    exact Subgroup.mul_mem_sup he hk
  exact le_of_pPrimePerfect_of_le_sup hF (hFY.trans hYE) hEΘ hΘ hle

end Six

end CFSG.LocalAnalysis.GLTheoremA.H301
