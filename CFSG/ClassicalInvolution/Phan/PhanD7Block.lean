module

public import CFSG.ClassicalInvolution.Phan.PhanD6Inf
import CFSG.ClassicalInvolution.Phan.Parabolic.Generic

public section

namespace CFSG.ClassicalInvolution.PhanD4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {Y : Type} [Group Y] (S : PhanFamilyD4 K p f G)
  (F : PhanFamilyD4 K p f Y)

@[expose] noncomputable def Lsup (J : Set (Fin 4)) : Subgroup G := ⨆ j ∈ J, (S.ι j).range

@[expose] noncomputable def parab (J : Set (Fin 4)) : Subgroup G := torusSub S ⊔ Lsup S J

variable {S F}

theorem ι_mem_Lsup {J : Set (Fin 4)} {j : Fin 4} (hj : j ∈ J) (A : Su K p f 2) :
    S.ι j A ∈ Lsup S J :=
  (le_iSup₂ (f := fun j _ => (S.ι j).range) j hj) ⟨A, rfl⟩

theorem torusSub_le_parab (J : Set (Fin 4)) : torusSub S ≤ parab S J := le_sup_left

theorem Lsup_le_parab (J : Set (Fin 4)) : Lsup S J ≤ parab S J := le_sup_right

theorem Lsup_empty : Lsup S (∅ : Set (Fin 4)) = ⊥ := by simp [Lsup]

theorem Lsup_singleton (i : Fin 4) : Lsup S {i} = (S.ι i).range := by simp [Lsup]

theorem Lsup_pair (a b : Fin 4) : Lsup S {a, b} = (S.ι a).range ⊔ (S.ι b).range := by
  exact iSup_pair (f := fun j => (S.ι j).range)

theorem Lsup_mono {J J' : Set (Fin 4)} (h : J ⊆ J') : Lsup S J ≤ Lsup S J' :=
  iSup₂_le fun j hj => le_iSup₂ (f := fun j _ => (S.ι j).range) j (h hj)

theorem parab_mono {J J' : Set (Fin 4)} (h : J ⊆ J') : parab S J ≤ parab S J' :=
  sup_le_sup_left (Lsup_mono h) _

theorem torusSub_le_normalizer_range (hK : Nat.card K = (p ^ f) ^ 2) (j : Fin 4) :
    torusSub S ≤ Subgroup.normalizer ((S.ι j).range : Set G) := by
  have key : ∀ t : Fin 4 → normOne (unitaryInvolution K p f), ∀ x ∈ (S.ι j).range,
      mTor S t * x * (mTor S t)⁻¹ ∈ (S.ι j).range := by
    rintro t _ ⟨A, rfl⟩
    rw [mTor_conj_ι hK]
    exact ⟨_, rfl⟩
  rintro _ ⟨t, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t x, fun hx => ?_⟩
  have := key t⁻¹ _ hx
  rw [map_inv] at this
  simpa [mul_assoc] using this

theorem torusSub_le_normalizer_Lsup (hK : Nat.card K = (p ^ f) ^ 2) (J : Set (Fin 4)) :
    torusSub S ≤ Subgroup.normalizer (Lsup S J : Set G) :=
  le_normalizer_iSup₂ _ J _ (torusSub_le_normalizer_range hK)

@[expose] def IsBlockHom (J : Set (Fin 4)) (φN : Lsup S J →* Y) : Prop :=
  ∀ (j : Fin 4) (hj : j ∈ J) (A : Su K p f 2), φN ⟨S.ι j A, ι_mem_Lsup hj A⟩ = F.ι j A

section Exists

@[expose] noncomputable def rangeHom (hg : GoodFamily S) (F : PhanFamilyD4 K p f Y) (i : Fin 4) :
    (S.ι i).range →* Y :=
  (F.ι i).comp (MonoidHom.ofInjective (hg.inj i)).symm.toMonoidHom

theorem rangeHom_apply (hg : GoodFamily S) (i : Fin 4) (x : (S.ι i).range) (A : Su K p f 2)
    (h : (x : G) = S.ι i A) : rangeHom hg F i x = F.ι i A := by
  obtain ⟨x, hx⟩ := x
  subst h
  simp only [rangeHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ofInjective_symm_apply_self]

variable (hg : GoodFamily S)

theorem exists_blockHom_empty : ∃ φN : Lsup S (∅ : Set (Fin 4)) →* Y, IsBlockHom (F := F) ∅ φN :=
  ⟨1, fun _ hj => absurd hj (by simp)⟩

include hg in
theorem exists_blockHom_singleton (i : Fin 4) :
    ∃ φN : Lsup S {i} →* Y, IsBlockHom (F := F) {i} φN := by
  refine ⟨(rangeHom hg F i).comp
    (MulEquiv.subgroupCongr (Lsup_singleton (S := S) i)).toMonoidHom, ?_⟩
  intro j hj A
  obtain rfl : j = i := hj
  exact rangeHom_apply hg j _ A rfl

include hg in
theorem exists_blockHom_edge (hK : Nat.card K = (p ^ f) ^ 2) (e : Fin 3) {J : Set (Fin 4)}
    (hJ : J = {edgeSrc e, edgeTgt e}) : ∃ φN : Lsup S J →* Y, IsBlockHom (F := F) J φN := by
  have hle : Lsup S J ≤ (S.θ e).range := by
    rw [hJ]
    refine iSup₂_le fun j hj => ?_
    rcases hj with hj | hj
    · subst hj
      rintro _ ⟨A, rfl⟩
      exact ⟨embSUid (unitaryInvolution K p f) 2 A, (ι_src S e A).symm⟩
    · obtain rfl : j = edgeTgt e := hj
      rintro _ ⟨A, rfl⟩
      exact ⟨embSUid (unitaryInvolution K p f) 0 A, (ι_tgt S e A).symm⟩
  let ψ : Lsup S J →* Y :=
    ((F.θ e).comp (MonoidHom.ofInjective (hg.θ_injective hK e)).symm.toMonoidHom).comp
      (Subgroup.inclusion hle)
  have hψ : ∀ (x : Lsup S J) (B : Su K p f 3), (x : G) = S.θ e B → ψ x = F.θ e B := by
    intro x B hxB
    obtain ⟨x, hx⟩ := x
    subst hxB
    exact congrArg (F.θ e) (ofInjective_symm_apply_self (hg.θ_injective hK e) B _)
  refine ⟨ψ, fun j hj A => ?_⟩
  rw [hJ] at hj
  rcases hj with hj | hj
  · subst hj
    exact (hψ _ (embSUid (unitaryInvolution K p f) 2 A) (ι_src S e A)).trans
      (ι_src F e A).symm
  · obtain rfl : j = edgeTgt e := hj
    exact (hψ _ (embSUid (unitaryInvolution K p f) 0 A) (ι_tgt S e A)).trans
      (ι_tgt F e A).symm

theorem range_commute_of_far {a b : Fin 4} (hab : a ≠ b) (h1 : ¬ edgeD 4 a b)
    (h2 : ¬ edgeD 4 b a) : ∀ x ∈ (S.ι a).range, ∀ y ∈ (S.ι b).range, x * y = y * x := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact S.comm a b hab h1 h2 A B

theorem range_le_normalizer_of_far {a b : Fin 4} (hab : a ≠ b) (h1 : ¬ edgeD 4 a b)
    (h2 : ¬ edgeD 4 b a) : (S.ι b).range ≤ Subgroup.normalizer ((S.ι a).range : Set G) :=
  le_trans (fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
    range_commute_of_far hab h1 h2 x hx y hy) (Subgroup.centralizer_le_normalizer _)

include hg in
theorem exists_blockHom_far {a b : Fin 4} (hab : a ≠ b) (h1 : ¬ edgeD 4 a b) (h2 : ¬ edgeD 4 b a) :
    ∃ φN : Lsup S {a, b} →* Y, IsBlockHom (F := F) {a, b} φN := by
  have hcomm := range_commute_of_far (S := S) hab h1 h2
  have hNT := range_le_normalizer_of_far (S := S) hab h1 h2
  obtain ⟨φ, hφ1, hφ2⟩ := exists_hom_sup_of_normalizes hNT (rangeHom hg F a) (rangeHom hg F b)
    (fun g hN hT => by
      have hg1 : g ∈ (S.ι a).range ⊓ (S.ι b).range := ⟨hN, hT⟩
      rw [hg.disj a b hab, Subgroup.mem_bot] at hg1
      subst hg1
      have e1 : (⟨1, hN⟩ : (S.ι a).range) = 1 := rfl
      have e2 : (⟨1, hT⟩ : (S.ι b).range) = 1 := rfl
      rw [e1, e2, map_one, map_one])
    (fun t n => by
      obtain ⟨_, B, rfl⟩ := t
      obtain ⟨_, A, rfl⟩ := n
      have hc : conjAutOfNormalizer hNT ⟨S.ι b B, B, rfl⟩ ⟨S.ι a A, A, rfl⟩ =
          ⟨S.ι a A, A, rfl⟩ := by
        refine Subtype.ext ?_
        rw [coe_conjAutOfNormalizer]
        exact mul_inv_eq_iff_eq_mul.2 (hcomm _ ⟨A, rfl⟩ _ ⟨B, rfl⟩).symm
      rw [hc, rangeHom_apply hg b _ B rfl, rangeHom_apply hg a _ A rfl]
      exact mul_inv_eq_iff_eq_mul.2 (F.comm b a hab.symm h2 h1 B A))
  refine ⟨φ.comp (MulEquiv.subgroupCongr (Lsup_pair (S := S) a b).symm).symm.toMonoidHom, ?_⟩
  intro j hj A
  rcases hj with hj | hj
  · subst hj
    exact (hφ1 ⟨S.ι j A, A, rfl⟩).trans (rangeHom_apply hg j _ A rfl)
  · obtain rfl : j = b := hj
    exact (hφ2 ⟨S.ι j A, A, rfl⟩).trans (rangeHom_apply hg j _ A rfl)

include hg in
theorem exists_blockHom (hK : Nat.card K = (p ^ f) ^ 2) {J : Set (Fin 4)} (hJ : J.encard ≤ 2) :
    ∃ φN : Lsup S J →* Y, IsBlockHom (F := F) J φN := by
  rcases hJ.lt_or_eq with h | h
  · have h1 : J.encard ≤ 1 := by
      have : (2 : ℕ∞) = 1 + 1 := by norm_num
      rw [this] at h
      exact (ENat.lt_add_one_iff (by simp)).1 h
    rcases Set.encard_le_one_iff_eq.1 h1 with rfl | ⟨a, rfl⟩
    · exact exists_blockHom_empty
    · exact exists_blockHom_singleton hg a
  · obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.1 h
    by_cases h1 : edgeD 4 a b
    · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff a b).1 h1
      exact exists_blockHom_edge hg hK e rfl
    by_cases h2 : edgeD 4 b a
    · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff b a).1 h2
      obtain ⟨φN, hφN⟩ := exists_blockHom_edge (F := F) hg hK e (J := {edgeSrc e, edgeTgt e}) rfl
      have hpair : Lsup S {edgeTgt e, edgeSrc e} = Lsup S {edgeSrc e, edgeTgt e} := by
        rw [Set.pair_comm]
      refine ⟨φN.comp (MulEquiv.subgroupCongr hpair).toMonoidHom, ?_⟩
      intro j hj A
      exact hφN j (by rwa [Set.pair_comm]) A
    · exact exists_blockHom_far hg hab h1 h2

end Exists

section Agree

theorem Lsup_edge_le (e : Fin 3) : Lsup S {edgeSrc e, edgeTgt e} ≤ (S.θ e).range := by
  refine iSup₂_le fun j hj => ?_
  rcases hj with hj | hj
  · subst hj
    rintro _ ⟨A, rfl⟩
    exact ⟨embSUid (unitaryInvolution K p f) 2 A, (ι_src S e A).symm⟩
  · obtain rfl : j = edgeTgt e := hj
    rintro _ ⟨A, rfl⟩
    exact ⟨embSUid (unitaryInvolution K p f) 0 A, (ι_tgt S e A).symm⟩

theorem IsBlockHom.agree_of_factor (hinj : Function.Injective (mTor S)) {J : Set (Fin 4)}
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (F := F) J φN) {a b : Fin 4} (ha : a ∈ J)
    (hb : b ∈ J) (t : Fin 4 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J)
    (y w : normOne (unitaryInvolution K p f)) (h : mTor S t = tor S a y * tor S b w) :
    φN ⟨mTor S t, hmem⟩ = mTor F t := by
  have ht : t = Pi.mulSingle a y * Pi.mulSingle b w :=
    hinj (by rw [h, map_mul, mTor_mulSingle, mTor_mulSingle])
  have hprod : (⟨mTor S t, hmem⟩ : Lsup S J) =
      ⟨S.ι a (torusTwo (unitaryInvolution K p f) y), ι_mem_Lsup ha _⟩ *
        ⟨S.ι b (torusTwo (unitaryInvolution K p f) w), ι_mem_Lsup hb _⟩ :=
    Subtype.ext h
  rw [hprod, map_mul, hφ a ha, hφ b hb, ht, map_mul, mTor_mulSingle, mTor_mulSingle]
  rfl

variable (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f) (hg : GoodFamily S)

include hK hq hg in
theorem IsBlockHom.agree_edge (e : Fin 3) {J : Set (Fin 4)} (hJ : J = {edgeSrc e, edgeTgt e})
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (F := F) J φN) (h2 : (2 : K) ≠ 0)
    (t : Fin 4 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J) :
    φN ⟨mTor S t, hmem⟩ = mTor F t := by
  have hmem' : mTor S t ∈ (S.θ e).range := by
    rw [hJ] at hmem
    exact Lsup_edge_le e hmem
  obtain ⟨B, hB⟩ := hmem'
  obtain ⟨y, w, hyw⟩ := hg.exists_tor_of_theta hK hq e (B := B)
    (by rw [hB]; exact mTor_mem_torusSub S t)
  refine hφ.agree_of_factor (hg.mTor_injective hK h2) (a := edgeSrc e) (b := edgeTgt e)
    (by rw [hJ]; exact Or.inl rfl) (by rw [hJ]; exact Or.inr rfl) t hmem y w ?_
  rw [← hB, hyw]

include hK hq hg in
theorem IsBlockHom.agree (h2 : (2 : K) ≠ 0) {J : Set (Fin 4)} (hJ : J.encard ≤ 2)
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (F := F) J φN)
    (t : Fin 4 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J) :
    φN ⟨mTor S t, hmem⟩ = mTor F t := by
  have hinj := hg.mTor_injective hK h2
  rcases hJ.lt_or_eq with h | h
  · have h1 : J.encard ≤ 1 := by
      have : (2 : ℕ∞) = 1 + 1 := by norm_num
      rw [this] at h
      exact (ENat.lt_add_one_iff (by simp)).1 h
    rcases Set.encard_le_one_iff_eq.1 h1 with rfl | ⟨a, rfl⟩
    · have h1 : mTor S t = 1 := by
        have := hmem
        rw [Lsup_empty, Subgroup.mem_bot] at this
        exact this
      have ht : t = 1 := hinj (by rw [h1, map_one])
      have : (⟨mTor S t, hmem⟩ : Lsup S ∅) = 1 := Subtype.ext h1
      rw [this, map_one, ht, map_one]
    · have hmem' : mTor S t ∈ (S.ι a).range := by
        rw [← Lsup_singleton]
        exact hmem
      obtain ⟨A, hA⟩ := hmem'
      obtain ⟨y, hy⟩ := hg.exists_tor_of_mem_range hK hq a (A := A)
        (by rw [hA]; exact mTor_mem_torusSub S t)
      refine hφ.agree_of_factor hinj (a := a) (b := a) rfl rfl t hmem y 1 ?_
      rw [map_one, mul_one, ← hA, hy]
  · obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.1 h
    by_cases h1 : edgeD 4 a b
    · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff a b).1 h1
      exact hφ.agree_edge hK hq hg e rfl h2 t hmem
    by_cases h2' : edgeD 4 b a
    · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff b a).1 h2'
      exact hφ.agree_edge hK hq hg e (Set.pair_comm _ _) h2 t hmem
    · have hNT := range_le_normalizer_of_far (S := S) hab h1 h2'
      have hmem' : mTor S t ∈ ((S.ι a).range ⊔ (S.ι b).range : Subgroup G) := by
        rw [← Lsup_pair]
        exact hmem
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hNT] at hmem'
      obtain ⟨x, ⟨A, rfl⟩, z, ⟨B, rfl⟩, hxz0⟩ := hmem'
      have hxz : S.ι a A * S.ι b B = mTor S t := hxz0
      obtain ⟨y, w, hyw⟩ := hg.exists_tor_of_pair hK hq hab h1 h2' (A := A) (B := B)
        (by rw [hxz]; exact mTor_mem_torusSub S t)
      exact hφ.agree_of_factor hinj (a := a) (b := b) (Or.inl rfl) (Or.inr rfl) t hmem y w
        (by rw [← hxz, hyw])

end Agree

end CFSG.ClassicalInvolution.PhanD4
