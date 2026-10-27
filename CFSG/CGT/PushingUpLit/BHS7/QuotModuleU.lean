module

public import CFSG.CGT.PushingUpLit.BHS.FourSymI
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixAsm
public import CFSG.CGT.PushingUpLit.BHS6.Basic
public import CFSG.CGT.PushingUpLit.BHS7.QuotAutOn
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

section Aut

variable {M : Type} [CommGroup M] [Finite M]

theorem wt_eq_card_of_isOff (hM : ∀ v : M, v ^ 2 = 1)
    {P T N : Subgroup (MulAut M)} (hmin : MinPar P T N) (ho2 : pCoreOf 2 P = ⊥)
    {A : Subgroup (MulAut M)} (hAT : A ≤ T) (hoff : IsOff A) : wt A = Nat.card M := by
  have hAA : A ≤ P := hAT.trans hmin.T_le
  obtain ⟨g, hg, u, hu, hgu⟩ := BHS5.five_six bhsSymType hM hmin ho2 ⟨A, hAA, hoff⟩
  have hfix : ∀ v ∈ fixV T, ∀ x ∈ T, x v = v := fun v hv x hx => by
    have := (mem_fixV_iff_le.mp hv) hx
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  have hcen : cenIn P (fixV T) ≤ N := by
    set X := cenIn P (fixV T) with hX
    have hTX : T ≤ X := fun t ht => ⟨hmin.T_le ht, fun v hv => hfix v hv t ht⟩
    have hXP : X ≤ P := cenIn_le _ _
    have hXlt : X < P := lt_of_le_of_ne hXP fun hEq => hgu (by
      have hgX : g ∈ X := hEq ▸ hg
      exact hgX.2 u hu)
    exact hmin.max X hTX hXlt
  obtain ⟨B, hB⟩ := exists_isAOff ⟨A, hAA, hoff⟩
  have hnum := three_six_numeric hM hmin ho2 hcen hB
  have hle : wt A ≤ offMax P := wt_le_offMax hAA hoff
  have hBw : Nat.card M = wt B := hnum.card
  have hBmax : wt B = offMax P := hB.2.2.1
  have hge : Nat.card M ≤ wt A := hoff.card_le_wt
  omega

theorem wt_le_card_of_minPar (hM : ∀ v : M, v ^ 2 = 1)
    {P T N : Subgroup (MulAut M)} (hmin : MinPar P T N) (ho2 : pCoreOf 2 P = ⊥)
    {A : Subgroup (MulAut M)} (hAT : A ≤ T) (hA : IsElemAbelian2 A) : wt A ≤ Nat.card M := by
  obtain ⟨A₀, hA₀, hmax⟩ := Set.exists_max_image {B : Subgroup (MulAut M) | B ≤ A}
    (fun B => wt B) (Set.toFinite _) ⟨⊥, (bot_le : ⊥ ≤ A)⟩
  refine (hmax A (le_rfl : A ≤ A)).trans ?_
  by_cases hbot : A₀ = ⊥
  · rw [hbot]
    exact (B1.card_bot_mul_card_fixV (V := M)).le
  · have hoff : IsOff A₀ :=
      ⟨le_top, hbot, isElemAbelian2_mono' hA hA₀, fun C hC => hmax C (hC.trans hA₀)⟩
    exact (wt_eq_card_of_isOff hM hmin ho2 (hA₀.trans hAT) hoff).le

end Aut

section Sec

variable {V : Type} [CommGroup V]

@[expose] def secFix (B : Subgroup (MulAut V)) (X Y : Subgroup V) : Subgroup V where
  carrier := {x | x ∈ X ∧ ∀ b ∈ B, b x * x⁻¹ ∈ Y}
  mul_mem' := by
    rintro x y ⟨hx, hxb⟩ ⟨hy, hyb⟩
    refine ⟨X.mul_mem hx hy, fun b hb => ?_⟩
    have : b (x * y) * (x * y)⁻¹ = (b x * x⁻¹) * (b y * y⁻¹) := by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _
    rw [this]
    exact Y.mul_mem (hxb b hb) (hyb b hb)
  one_mem' := ⟨X.one_mem, fun b _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxb⟩
    refine ⟨X.inv_mem hx, fun b hb => ?_⟩
    have : b x⁻¹ * x⁻¹⁻¹ = (b x * x⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
    rw [this]
    exact Y.inv_mem (hxb b hb)

theorem mem_secFix {B : Subgroup (MulAut V)} {X Y : Subgroup V} {x : V} :
    x ∈ secFix B X Y ↔ x ∈ X ∧ ∀ b ∈ B, b x * x⁻¹ ∈ Y := Iff.rfl

theorem secFix_mono_right {B : Subgroup (MulAut V)} {X Y Y' : Subgroup V} (h : Y ≤ Y') :
    secFix B X Y ≤ secFix B X Y' := fun _ hx => ⟨hx.1, fun b hb => h (hx.2 b hb)⟩

end Sec

section QIdx

variable {V : Type} [CommGroup V]

theorem relIndex_fixV_qImg {K B : Subgroup (MulAut V)} (hBK : B ≤ K) (X : Subgroup V) :
    (fixV (qImg K B)).relIndex (X.map (QuotientGroup.mk' (BHS5.fixOp K))) =
      (secFix B X (BHS5.fixOp K)).relIndex X := by
  have h1 : (fixV (qImg K B)).comap (QuotientGroup.mk' (BHS5.fixOp K)) ⊓ X =
      secFix B X (BHS5.fixOp K) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, mem_secFix]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx2, fun b hb => ?_⟩
      have := hx1 (BHS5.quotHom K ⟨b, hBK hb⟩) (mem_qImg.2 ⟨⟨b, hBK hb⟩, hb, rfl⟩)
      exact (quotHom_apply_mk_eq_iff ⟨b, hBK hb⟩ x).1 this
    · rintro ⟨hx2, hx⟩
      refine ⟨fun y hy => ?_, hx2⟩
      obtain ⟨z, hz, rfl⟩ := mem_qImg.1 hy
      exact (quotHom_apply_mk_eq_iff z x).2 (hx z hz)
  rw [← h1, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]

end QIdx

section SecMod

variable {V : Type} [CommGroup V]

abbrev SecMod (X Y : Subgroup V) : Type := ↥X ⧸ Y.subgroupOf X

@[expose] noncomputable def secAct (X Y : Subgroup V) :
    ↥(stabSub X ⊓ stabSub Y) →* MulAut (SecMod X Y) :=
  (BHS5.quotAct (Y.subgroupOf X)).comp
    (((resHom X).comp (Subgroup.inclusion inf_le_left)).codRestrict
      (stabSub (Y.subgroupOf X)) (fun g u => by
        show ((g : MulAut V) u : V) ∈ Y ↔ (u : V) ∈ Y
        exact g.2.2 u))

theorem mem_ker_secAct (X Y : Subgroup V) (g : ↥(stabSub X ⊓ stabSub Y)) :
    g ∈ (secAct X Y).ker ↔ ∀ u ∈ X, (g : MulAut V) u * u⁻¹ ∈ Y := by
  have h := BHS5.mem_ker_quotAct (Y.subgroupOf X)
    (⟨(resHom X) (Subgroup.inclusion inf_le_left g), fun u => by
      show ((g : MulAut V) u : V) ∈ Y ↔ (u : V) ∈ Y
      exact g.2.2 u⟩ : ↥(stabSub (Y.subgroupOf X)))
  show (⟨(resHom X) (Subgroup.inclusion inf_le_left g), fun u => by
      show ((g : MulAut V) u : V) ∈ Y ↔ (u : V) ∈ Y
      exact g.2.2 u⟩ : ↥(stabSub (Y.subgroupOf X))) ∈ (BHS5.quotAct (Y.subgroupOf X)).ker ↔ _
  rw [h]
  constructor
  · intro H u hu
    exact Subgroup.mem_subgroupOf.1 (H ⟨u, hu⟩)
  · intro H u
    exact Subgroup.mem_subgroupOf.2 (H u u.2)

end SecMod

section UAbs

variable {V : Type} [CommGroup V] {X Y : Subgroup V} {S : Type} [Group S]

@[expose] noncomputable def secActOf (ψ : S →* MulAut V)
    (hψ : ∀ g, ψ g ∈ stabSub X ⊓ stabSub Y) : S →* MulAut (SecMod X Y) :=
  (secAct X Y).comp (ψ.codRestrict (stabSub X ⊓ stabSub Y) hψ)

theorem secActOf_mk (ψ : S →* MulAut V) (hψ : ∀ g, ψ g ∈ stabSub X ⊓ stabSub Y) (g : S)
    (u : ↥X) :
    secActOf ψ hψ g (QuotientGroup.mk u) =
      (QuotientGroup.mk ⟨ψ g u, ((hψ g).1 u).2 u.2⟩ : SecMod X Y) := rfl

theorem mem_ker_secActOf (ψ : S →* MulAut V) (hψ : ∀ g, ψ g ∈ stabSub X ⊓ stabSub Y) (g : S) :
    g ∈ (secActOf ψ hψ).ker ↔ ∀ u ∈ X, ψ g u * u⁻¹ ∈ Y :=
  mem_ker_secAct X Y ⟨ψ g, hψ g⟩

theorem secActOf_congr (ψ : S →* MulAut V) (hψ : ∀ g, ψ g ∈ stabSub X ⊓ stabSub Y) {g g' : S}
    (h : ψ g = ψ g') : secActOf ψ hψ g = secActOf ψ hψ g' := by
  unfold secActOf
  simp only [MonoidHom.comp_apply]
  congr 1
  exact Subtype.ext h

theorem mk_eq_mk_iff (a c : ↥X) :
    (QuotientGroup.mk a : SecMod X Y) = QuotientGroup.mk c ↔ ((a : V) * (c : V)⁻¹) ∈ Y := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rw [← Y.inv_mem_iff]
  simp [mul_comm]

end UAbs

section UAbs2

variable {V : Type} [CommGroup V] [Finite V] {X Y : Subgroup V} {S : Type} [Group S] [Finite S]

theorem relIndex_ker_le_secFix (hV : ∀ v : V, v ^ 2 = 1)
    (ψ : S →* MulAut V) (hψ : ∀ g, ψ g ∈ stabSub X ⊓ stabSub Y) {T' M' : Subgroup S}
    (hmin : MinPar (⊤ : Subgroup S) T' M') (hker : (secActOf ψ hψ).ker ⊓ ⊤ ≤ M')
    (hO2 : pCoreOf 2 (⊤ : Subgroup S) ≤ (secActOf ψ hψ).ker) {B : Subgroup S} (hBT : B ≤ T')
    (hBe : IsElemAbelian2 (B.map ψ)) :
    ((secActOf ψ hψ).ker ⊓ B).relIndex B ≤ (secFix (B.map ψ) X Y).relIndex X := by
  set u := secActOf ψ hψ with hu
  have hU2 : ∀ x : SecMod X Y, x ^ 2 = 1 :=
    BHS5.quot_sq_eq_one (fun v : ↥X => Subtype.ext (hV v)) _
  have hmin' := BHS5.MinPar.map_of_ker_le u hmin hker
  have hO2' := BHS5.pCoreOf_map_eq_bot_of_ker_le u hmin hker hO2
  have hBU : B.map u ≤ T'.map u := Subgroup.map_mono hBT
  have hBUe : IsElemAbelian2 (B.map u) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul]
      apply secActOf_congr ψ hψ
      rw [map_mul, map_mul]
      exact hBe.1 (ψ b) ⟨b, hb, rfl⟩ (ψ b') ⟨b', hb', rfl⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow]
      have h1 : u (b ^ 2) = u 1 := secActOf_congr ψ hψ (by
        rw [map_pow, map_one]
        exact hBe.2 (ψ b) ⟨b, hb, rfl⟩)
      rw [h1, map_one]
  have hwt := wt_le_card_of_minPar hU2 hmin' hO2' hBU hBUe
  set F : Subgroup (SecMod X Y) := fixV (B.map u) with hF
  have hcard : F.index * Nat.card F = Nat.card (SecMod X Y) := Subgroup.index_mul_card F
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have h1 : Nat.card (B.map u) ≤ F.index := by
    have : Nat.card (B.map u) * Nat.card F ≤ F.index * Nat.card F := by
      rw [hcard]
      exact hwt
    exact Nat.le_of_mul_le_mul_right this hFpos
  have h2 : Nat.card (B.map u) = (u.ker ⊓ B).relIndex B := by
    rw [Subgroup.inf_relIndex_right, ← MonoidHom.comap_bot, Subgroup.relIndex_comap,
      Subgroup.relIndex_bot_left]
  have hν : Function.Surjective (QuotientGroup.mk' (Y.subgroupOf X)) :=
    QuotientGroup.mk'_surjective _
  have h3 : F.comap (QuotientGroup.mk' (Y.subgroupOf X)) =
      (secFix (B.map ψ) X Y).subgroupOf X := by
    ext w
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_secFix, hF]
    constructor
    · intro hw
      refine ⟨w.2, ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have h5 : u b (QuotientGroup.mk w) = QuotientGroup.mk w := hw (u b) ⟨b, hb, rfl⟩
      rw [hu, secActOf_mk] at h5
      exact (mk_eq_mk_iff _ w).1 h5
    · rintro ⟨hwX, hw⟩ a ⟨b, hb, rfl⟩
      show u b (QuotientGroup.mk w) = QuotientGroup.mk w
      rw [hu, secActOf_mk]
      exact (mk_eq_mk_iff _ w).2 (hw (ψ b) ⟨b, hb, rfl⟩)
  have h4 : (F.comap (QuotientGroup.mk' (Y.subgroupOf X))).index = F.index :=
    Subgroup.index_comap_of_surjective F hν
  rw [← h2]
  refine h1.trans ?_
  rw [← h4, h3]
  exact le_of_eq rfl

end UAbs2

end CFSG.CGT.PushingUpLit.BHS7
