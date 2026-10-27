module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldSignalizerSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldStrong
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvSylow
public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.CGT.Timmesfeld75.ListWCLinPSL
public import CFSG.LargeExtraspecial.S5Syl
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverLift
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldSignalizer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.X7a (up3 up3_zero)
open CFSG.Quasithin.SteinbergBS (mem_projCenter_iff mem_uniCenter proj_up3_inj up3_mul_self)
open CFSG.GH74.Generic.BProg.B2.GenLocL3Pair (rt)
open CFSG.LargeExtraspecial.S5 (IsSylowTwoIn exists_isSylowTwoIn_ge)

section Lift

variable {X L : Type*} [Group X] [Finite X] [Group L]

theorem injOn_of_isPGroup (ρ : X →* L) (hU : Odd (Nat.card ρ.ker)) {T : Subgroup X}
    (hT : IsPGroup 2 T) : Set.InjOn ρ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx y hy hxy
  have hcop : Nat.Coprime (Nat.card ρ.ker) (Nat.card T) := by
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hU)
  have hk : x⁻¹ * y ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have h : x⁻¹ * y ∈ ρ.ker ⊓ T := mem_inf.mpr ⟨hk, T.mul_mem (T.inv_mem hx) hy⟩
  rw [Subgroup.inf_eq_bot_of_coprime hcop, mem_bot] at h
  exact inv_mul_eq_one.mp h

theorem exists_lift_of_isPGroup (ρ : X →* L)
    (hρ : Function.Surjective ρ) (hU : Odd (Nat.card ρ.ker)) {V : Subgroup L}
    (hV : IsPGroup 2 V) {B : Subgroup X} (hB : IsPGroup 2 B) (hBV : B.map ρ ≤ V) :
    ∃ T : Subgroup X, B ≤ T ∧ IsPGroup 2 T ∧ T.map ρ = V ∧ Set.InjOn ρ T := by
  have : Finite L := Finite.of_surjective ρ hρ
  obtain ⟨T, hT, hBT⟩ := exists_isSylowTwoIn_ge (map_le_iff_le_comap.mp hBV) hB
  have hTV := hT.map ρ
  rw [map_comap_eq_self_of_surjective hρ] at hTV
  exact ⟨T, hBT, hT.isPGroup, (hTV.eq_of_le hTV.le le_rfl hV).symm,
    injOn_of_isPGroup ρ hU hT.isPGroup⟩

end Lift

section Gluing

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {R : Subgroup G} {g : G}
    (hg : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer ((R ⊓ centralizer (R : Set G) : Subgroup G) : Set G) := by
  have key : ∀ {k : G}, k ∈ normalizer (R : Set G) → ∀ h ∈ R ⊓ centralizer (R : Set G),
      k * h * k⁻¹ ∈ R ⊓ centralizer (R : Set G) := by
    intro k hk h ⟨hR, hC⟩
    refine ⟨(mem_normalizer_iff.mp hk h).mp hR, mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hr' : k⁻¹ * r * k ∈ R := by
      have := (mem_normalizer_iff.mp (inv_mem hk) r).mp hr
      rwa [inv_inv] at this
    have hc : k⁻¹ * r * k * h = h * (k⁻¹ * r * k) := mem_centralizer_iff.mp hC _ hr'
    calc r * (k * h * k⁻¹) = k * (k⁻¹ * r * k * h) * k⁻¹ := by group
      _ = k * (h * (k⁻¹ * r * k)) * k⁻¹ := by rw [hc]
      _ = k * h * k⁻¹ * r := by group
  refine mem_normalizer_iff.mpr fun h => ⟨key hg h, fun hh => ?_⟩
  have h1 := key (inv_mem hg) _ hh
  have h2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [h2] at h1

variable {F : Type} [Field F] [Finite F] [CharP F 2]
  {P : Subgroup G} {ρ : ↥P →* projectiveSL 3 F} {R : Subgroup G}

omit [Finite F] [CharP F 2] in
theorem mem_inf_centralizer_iff_of_map_eq (hU : Odd (Nat.card ρ.ker)) (hRP : R ≤ P)
    (hR2 : IsPGroup 2 R) (hRU : (R.subgroupOf P).map ρ = projUnitriangular 3 F) (a : ↥P) :
    (a : G) ∈ R ⊓ centralizer (R : Set G) ↔
      (a : G) ∈ R ∧ ∃ y : F, ρ a = proj 3 F (up3 0 y 0) := by
  have hinj := injOn_of_isPGroup ρ hU (hR2.of_equiv (subgroupOfEquivOfLe hRP).symm)
  constructor
  · rintro ⟨ha, hC⟩
    refine ⟨ha, ?_⟩
    have haU : ρ a ∈ projUnitriangular 3 F := hRU ▸ mem_map_of_mem ρ ha
    have hcomm : ∀ h ∈ projUnitriangular 3 F, ρ a * h = h * ρ a := by
      rw [← hRU]
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (mem_centralizer_iff.mp hC _ hr).symm)
    obtain ⟨u, hu, hua⟩ := mem_projCenter_iff.mpr ⟨haU, hcomm⟩
    obtain ⟨y, rfl⟩ := mem_uniCenter.mp hu
    exact ⟨y, hua.symm⟩
  · rintro ⟨ha, y, hy⟩
    refine ⟨ha, mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hz := (mem_projCenter_iff.mp ⟨up3 0 y 0, mem_uniCenter.mpr ⟨y, rfl⟩, rfl⟩).2
    have hr' : (⟨r, hRP hr⟩ : ↥P) ∈ R.subgroupOf P := hr
    have hrU : ρ ⟨r, hRP hr⟩ ∈ projUnitriangular 3 F := hRU ▸ mem_map_of_mem ρ hr'
    have := hinj (mul_mem hr' ha) (mul_mem ha hr') (by
      rw [map_mul, map_mul, hy]
      exact (hz _ hrU).symm)
    exact congrArg Subtype.val this

omit [Finite F] in
theorem isElemTwo_inf_centralizer_of_map_eq (hU : Odd (Nat.card ρ.ker)) (hRP : R ≤ P)
    (hR2 : IsPGroup 2 R) (hRU : (R.subgroupOf P).map ρ = projUnitriangular 3 F) :
    IsElemTwo (R ⊓ centralizer (R : Set G)) ∧
      Nat.card ↥(R ⊓ centralizer (R : Set G)) = Nat.card F := by
  have hinj := injOn_of_isPGroup ρ hU (hR2.of_equiv (subgroupOfEquivOfLe hRP).symm)
  have key := mem_inf_centralizer_iff_of_map_eq hU hRP hR2 hRU
  refine ⟨⟨fun x hx y hy => mem_centralizer_iff.mp hy.2 x hx.1, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨hxR, y, hy⟩ := (key ⟨x, hRP hx.1⟩).mp hx
    have hxR' : (⟨x, hRP hx.1⟩ : ↥P) ∈ R.subgroupOf P := hxR
    have := hinj (mul_mem hxR' hxR') (one_mem _) (by
      rw [map_mul, hy, map_one, ← map_mul, up3_mul_self, zero_mul, up3_zero, map_one])
    exact congrArg Subtype.val this
  · have hex : ∀ a : ↥(R ⊓ centralizer (R : Set G)),
        ∃ y : F, ρ ⟨a, hRP a.2.1⟩ = proj 3 F (up3 0 y 0) :=
      fun a => ((key ⟨a, hRP a.2.1⟩).mp a.2).2
    choose f hf using hex
    refine Nat.card_eq_of_bijective f ⟨fun a b hab => ?_, fun y => ?_⟩
    · have := hinj (show (⟨a, hRP a.2.1⟩ : ↥P) ∈ R.subgroupOf P from a.2.1)
        (show (⟨b, hRP b.2.1⟩ : ↥P) ∈ R.subgroupOf P from b.2.1) (by rw [hf, hf, hab])
      exact Subtype.ext (congrArg (fun p : ↥P => (p : G)) this)
    · have hyU : proj 3 F (up3 0 y 0) ∈ (R.subgroupOf P).map ρ := by
        rw [hRU]
        exact (mem_projCenter_iff.mp ⟨up3 0 y 0, mem_uniCenter.mpr ⟨y, rfl⟩, rfl⟩).1
      obtain ⟨r, hr, hry⟩ := hyU
      have hrA : (r : G) ∈ R ⊓ centralizer (R : Set G) :=
        (key r).mpr ⟨mem_subgroupOf.mp hr, y, hry⟩
      refine ⟨⟨r, hrA⟩, ?_⟩
      have h2 : proj 3 F (up3 0 (f ⟨r, hrA⟩) 0) = proj 3 F (up3 0 y 0) :=
        (hf ⟨r, hrA⟩).symm.trans hry
      exact (proj_up3_inj h2).2.1

omit [Finite F] in
theorem le_normalizer_wGroup_of_map_eq (hB : GWTwoBalanced G) (hρ : Function.Surjective ρ)
    (hU : Odd (Nat.card ρ.ker)) (hF : 16 ≤ Nat.card F) (hRP : R ≤ P) (hR2 : IsPGroup 2 R)
    (hRU : (R.subgroupOf P).map ρ = projUnitriangular 3 F) :
    P ≤ normalizer (wGroup (R ⊓ centralizer (R : Set G)) : Set G) := by
  obtain ⟨hAe, hAc⟩ := isElemTwo_inf_centralizer_of_map_eq hU hRP hR2 hRU
  set A := R ⊓ centralizer (R : Set G) with hAdef
  have hA3 : IsAbelianTwoOfRank 3 A := hAe.isAbelianTwoOfRank (by omega)
  have hR2' : IsPGroup 2 (R.subgroupOf P) := hR2.of_equiv (subgroupOfEquivOfLe hRP).symm
  have hinjR := injOn_of_isPGroup ρ hU hR2'
  have hND : ∀ D : Subgroup G, D ≤ R → IsAbelianTwoOfRank 3 D →
      normalizer (D : Set G) ≤ normalizer (wGroup A : Set G) := fun D hDR hD g hg => by
    rw [← wGroup_eq_of_commute hB hD hA3 fun x hx y hy => mem_centralizer_iff.mp hy.2 x (hDR hx)]
    exact GrS4.mem_normalizer_wGroup hg
  have hRN : R ≤ normalizer (wGroup A : Set G) := fun r hr =>
    GrS4.mem_normalizer_wGroup (mem_normalizer_inf_centralizer (R.le_normalizer hr))
  have hUN : ρ.ker.map P.subtype ≤ normalizer (wGroup A : Set G) := by
    have : IsElementaryAbelian 2 ↥A :=
      LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one
        fun x hx => by rw [pow_two]; exact hAe.2 x hx
    have : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hPV : P ≤ normalizer (ρ.ker.map P.subtype : Set G) := by
      have h := Subgroup.le_normalizer_map (H := ρ.ker) P.subtype
      rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    have hodd : ¬ 2 ∣ Nat.card (ρ.ker.map P.subtype) := by
      rw [card_map_of_injective P.subtype_injective]
      exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hU)
    refine (RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (A := A)
      (V := ρ.ker.map P.subtype) (fun a ha => hPV (hRP ha.1)) hodd).trans
      (iSup_le fun D => iSup_le fun hD => ?_)
    refine inf_le_right.trans ((centralizer_le_normalizer _).trans (hND _ ?_ ?_))
    · exact (map_subtype_le D).trans inf_le_left
    · have hc : Nat.card (D.map A.subtype) * 2 = Nat.card A := by
        rw [card_map_of_injective A.subtype_injective, ← hD, card_mul_index]
      exact (hAe.mono (map_subtype_le D)).isAbelianTwoOfRank (by omega)
  set H := ((normalizer (wGroup A : Set G)).subgroupOf P).map ρ with hH
  have hUH : projUnitriangular 3 F ≤ H := by
    rw [← hRU]
    exact map_mono fun r hr => hRN hr
  have lift : ∀ (i j : Fin 3) (hij : i < j) (x : projectiveSL 3 F), x * x = 1 →
      (∀ r : F, Commute x (rt i j hij.ne r)) → x ∈ H := by
    intro i j hij x hx hxr
    set Y := (rtHom (F := F) i j hij.ne).range with hY
    have hYe : IsElemTwo Y := isElemTwo_range_rtHom (F := F) i j hij.ne
    have hV : IsElemTwo (Y ⊔ zpowers x) := hYe.sup (isElemTwo_zpowers hx) fun a ha b hb => by
      obtain ⟨s, rfl⟩ := ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
      exact ((hxr s.toAdd).zpow_left k).eq.symm
    set B := R ⊓ (Y.comap ρ).map P.subtype with hBdef
    have hBP : B ≤ P := inf_le_left.trans hRP
    have hBR : B.subgroupOf P ≤ R.subgroupOf P := fun b hb => hb.1
    have hBY : (B.subgroupOf P).map ρ = Y := by
      refine le_antisymm ?_ fun z hz => ?_
      · rintro _ ⟨b, hb, rfl⟩
        obtain ⟨y, hy, hyb⟩ := hb.2
        rw [show b = y from Subtype.ext hyb.symm]
        exact hy
      · obtain ⟨r, hr, rfl⟩ : z ∈ (R.subgroupOf P).map ρ :=
          hRU ▸ rtHom_range_le_projUnitriangular hij hz
        exact ⟨r, ⟨hr, r, hz, rfl⟩, rfl⟩
    have hBinj : Set.InjOn ρ (B.subgroupOf P) := hinjR.mono hBR
    have hBe : IsElemTwo B := by
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · have ha' : (⟨a, hBP ha⟩ : ↥P) ∈ B.subgroupOf P := ha
        have hb' : (⟨b, hBP hb⟩ : ↥P) ∈ B.subgroupOf P := hb
        have := hBinj (mul_mem ha' hb') (mul_mem hb' ha') (by
          rw [map_mul, map_mul]
          exact hYe.1 _ (hBY ▸ mem_map_of_mem ρ ha') _ (hBY ▸ mem_map_of_mem ρ hb'))
        exact congrArg Subtype.val this
      · have ha' : (⟨a, hBP ha⟩ : ↥P) ∈ B.subgroupOf P := ha
        have := hBinj (mul_mem ha' ha') (one_mem _) (by
          rw [map_mul, map_one]
          exact hYe.2 _ (hBY ▸ mem_map_of_mem ρ ha'))
        exact congrArg Subtype.val this
    have hBc : Nat.card B = Nat.card F := by
      rw [← card_range_rtHom (F := F) hij, ← hY, ← hBY,
        CGT.Timmesfeld75.card_map_of_injOn ρ fun a ha b hb h => hBinj ha hb h]
      exact (Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv).symm
    obtain ⟨T, hBT, -, hTV, hTinj⟩ := exists_lift_of_isPGroup ρ hρ hU hV.isPGroup
      (hR2'.to_le hBR) (by rw [hBY]; exact le_sup_left)
    have hTN : ∀ a ∈ T, (a : G) ∈ normalizer (wGroup A : Set G) := by
      intro a ha
      refine hND B inf_le_left (hBe.isAbelianTwoOfRank (by omega))
        (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => ?_))
      have hb' : (⟨b, hBP hb⟩ : ↥P) ∈ T := hBT hb
      have := hTinj (mul_mem hb' ha) (mul_mem ha hb') (by
        rw [map_mul, map_mul]
        exact hV.1 _ (hTV ▸ mem_map_of_mem ρ hb') _ (hTV ▸ mem_map_of_mem ρ ha))
      exact congrArg Subtype.val this
    obtain ⟨a, ha, hax⟩ : x ∈ T.map ρ := hTV ▸ mem_sup_right (mem_zpowers x)
    exact ⟨a, hTN a ha, hax⟩
  have hsq : ∀ (i j : Fin 3) (hij : i ≠ j) (s : F), rt i j hij s * rt i j hij s = 1 :=
    fun i j hij s => (isElemTwo_range_rtHom (F := F) i j hij).2 _ ⟨Multiplicative.ofAdd s, rfl⟩
  have htop : H = ⊤ := eq_top_of_projUnitriangular_le hUH
    (fun s => lift 1 2 (by decide) _ (hsq _ _ _ s) (commute_rt_one_zero_rt_one_two s))
    (fun s => lift 0 1 (by decide) _ (hsq _ _ _ s) (commute_rt_two_one_rt_zero_one s))
  intro p hp
  obtain ⟨q, hq, hqp⟩ : ρ ⟨p, hp⟩ ∈ H := htop ▸ mem_top _
  have hk : q⁻¹ * ⟨p, hp⟩ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqp, inv_mul_cancel]
  have := mul_mem (show (q : G) ∈ normalizer (wGroup A : Set G) from hq) (hUN ⟨_, hk, rfl⟩)
  simpa using this

theorem card_le_card_inf_centralizer_sq_of_map_eq (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Open.fusionOddCore ↥P) (hU : Odd (Nat.card ρ.ker)) (hRP : R ≤ P)
    (hR2 : IsPGroup 2 R) (hRU : (R.subgroupOf P).map ρ = projUnitriangular 3 F)
    {E : Subgroup G} (hE : IsElemTwo E) (hEP : E ≤ normalizer (P : Set G))
    (hER : E ≤ normalizer (R : Set G)) :
    Nat.card ↥(R ⊓ centralizer (R : Set G)) ≤
      Nat.card ↥(R ⊓ centralizer (R : Set G) ⊓ centralizer (E : Set G)) ^ 2 := by
  obtain ⟨hAe, -⟩ := isElemTwo_inf_centralizer_of_map_eq hU hRP hR2 hRU
  set A := R ⊓ centralizer (R : Set G) with hAdef
  have key := mem_inf_centralizer_iff_of_map_eq hU hRP hR2 hRU
  have hinjR := injOn_of_isPGroup ρ hU (hR2.of_equiv (subgroupOfEquivOfLe hRP).symm)
  have hcP : ∀ e ∈ E, ∀ p ∈ P, e * p * e⁻¹ ∈ P := fun e he p hp =>
    (mem_normalizer_iff.mp (hEP he) p).mp hp
  have hα : ∀ e (he : e ∈ E), ∃ α : MulAut (projectiveSL 3 F), ∀ p : ↥P,
      α (ρ p) = ρ ⟨e * p * e⁻¹, hcP e he p p.2⟩ := by
    intro e he
    have hPe : P.map (MulAut.conj e).toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp (hEP he)
    let c : ↥P ≃* ↥P := ((MulAut.conj e).subgroupMap P).trans (MulEquiv.subgroupCongr hPe)
    have hck : ρ.ker.map c.toMonoidHom = ρ.ker := by
      rw [hker]
      exact CGT.Timmesfeld75.fusionOddCore_map_mulEquiv c
    let q := QuotientGroup.quotientKerEquivOfSurjective ρ hρ
    refine ⟨q.symm.trans ((QuotientGroup.congr ρ.ker ρ.ker c hck).trans q), fun p => ?_⟩
    have h1 : q.symm (ρ p) = (p : ↥P ⧸ ρ.ker) := q.symm_apply_eq.mpr rfl
    simp only [MulEquiv.trans_apply, h1]
    rfl
  choose α hαp using hα
  have hinv : ∀ e ∈ E, e⁻¹ = e := fun e he => inv_eq_of_mul_eq_one_right (hE.2 e he)
  have hαU : ∀ e (he : e ∈ E),
      (projUnitriangular 3 F).map (α e he).toMonoidHom = projUnitriangular 3 F := by
    intro e he
    have hle : (projUnitriangular 3 F).map (α e he).toMonoidHom ≤ projUnitriangular 3 F := by
      rw [← hRU, map_map]
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp (hER he) r).mp hr, (hαp e he r).symm⟩
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (α e he).injective])
  have hZR : ∀ y : F, ∃ r : ↥P, r ∈ R.subgroupOf P ∧ ρ r = proj 3 F (up3 0 y 0) := fun y => by
    have : proj 3 F (up3 0 y 0) ∈ (R.subgroupOf P).map ρ := by
      rw [hRU]
      exact (mem_projCenter_iff.mp ⟨up3 0 y 0, mem_uniCenter.mpr ⟨y, rfl⟩, rfl⟩).1
    obtain ⟨r, hr, h⟩ := this
    exact ⟨r, hr, h⟩
  have hα2 : ∀ e (he : e ∈ E), ∀ y : F,
      α e he (α e he (proj 3 F (up3 0 y 0))) = proj 3 F (up3 0 y 0) := by
    intro e he y
    obtain ⟨r, -, hr⟩ := hZR y
    rw [← hr, hαp, hαp]
    congr 1
    apply Subtype.ext
    change e * (e * r * e⁻¹) * e⁻¹ = r
    rw [hinv e he]
    calc e * (e * r * e) * e = e * e * r * (e * e) := by group
      _ = r := by rw [hE.2 e he, one_mul, mul_one]
  have hαβ : ∀ e (he : e ∈ E) f (hf : f ∈ E), ∀ y : F,
      α e he (α f hf (α e he (α f hf (proj 3 F (up3 0 y 0))))) = proj 3 F (up3 0 y 0) := by
    intro e he f hf y
    obtain ⟨r, -, hr⟩ := hZR y
    rw [← hr, hαp, hαp, hαp, hαp]
    congr 1
    apply Subtype.ext
    change e * (f * (e * (f * r * f⁻¹) * e⁻¹) * f⁻¹) * e⁻¹ = r
    rw [hinv e he, hinv f hf]
    calc e * (f * (e * (f * r * f) * e) * f) * e = e * f * (e * f) * r * (f * e * (f * e)) := by
          group
      _ = r := by rw [hE.2 _ (mul_mem he hf), hE.2 _ (mul_mem hf he), one_mul, mul_one]
  have hfix : ∀ e (he : e ∈ E), (∀ y : F, α e he (proj 3 F (up3 0 y 0)) = proj 3 F (up3 0 y 0)) →
      ∀ a ∈ A, e * a = a * e := by
    intro e he h a ha
    obtain ⟨haR, y, hy⟩ := (key ⟨a, hRP ha.1⟩).mp ha
    have ha' : (⟨a, hRP ha.1⟩ : ↥P) ∈ R.subgroupOf P := haR
    have hea : (⟨e * a * e⁻¹, hcP e he a (hRP ha.1)⟩ : ↥P) ∈ R.subgroupOf P :=
      (mem_normalizer_iff.mp (hER he) a).mp haR
    have h1 := hαp e he ⟨a, hRP ha.1⟩
    rw [hy, h y] at h1
    have := hinjR hea ha' (h1.symm.trans hy.symm)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun p : ↥P => (p : G)) this)
  have heq : ∀ e (he : e ∈ E) f (hf : f ∈ E),
      (∀ y : F, α e he (proj 3 F (up3 0 y 0)) = α f hf (proj 3 F (up3 0 y 0))) →
      ∀ a ∈ A, e * a * e⁻¹ = f * a * f⁻¹ := by
    intro e he f hf h a ha
    obtain ⟨haR, y, hy⟩ := (key ⟨a, hRP ha.1⟩).mp ha
    have hea : (⟨e * a * e⁻¹, hcP e he a (hRP ha.1)⟩ : ↥P) ∈ R.subgroupOf P :=
      (mem_normalizer_iff.mp (hER he) a).mp haR
    have hfa : (⟨f * a * f⁻¹, hcP f hf a (hRP ha.1)⟩ : ↥P) ∈ R.subgroupOf P :=
      (mem_normalizer_iff.mp (hER hf) a).mp haR
    have h1 := hαp e he ⟨a, hRP ha.1⟩
    have h2 := hαp f hf ⟨a, hRP ha.1⟩
    rw [hy] at h1 h2
    rw [h y] at h1
    have := hinjR hea hfa (h1.symm.trans h2)
    exact congrArg (fun p : ↥P => (p : G)) this
  by_cases hall : ∀ e (he : e ∈ E), ∀ y : F,
      α e he (proj 3 F (up3 0 y 0)) = proj 3 F (up3 0 y 0)
  · have : A ⊓ centralizer (E : Set G) = A := inf_eq_left.mpr fun a ha =>
      mem_centralizer_iff.mpr fun e he => hfix e he (hall e he) a ha
    rw [this]
    exact Nat.le_self_pow two_ne_zero _
  push Not at hall
  obtain ⟨e₀, he₀, y₀, hy₀⟩ := hall
  have hle : A ⊓ centralizer ({e₀} : Set G) ≤ A ⊓ centralizer (E : Set G) := by
    rintro a ⟨ha, ha₀⟩
    refine ⟨ha, mem_centralizer_iff.mpr fun f hf => ?_⟩
    have ha₀' : e₀ * a = a * e₀ := (mem_centralizer_singleton_iff.mp ha₀).symm
    rcases center_trichotomy (hαU e₀ he₀) (hαU f hf) (hα2 e₀ he₀) (hα2 f hf)
      (hαβ e₀ he₀ f hf) with h | h | h
    · exact absurd (h y₀) hy₀
    · exact hfix f hf h a ha
    · have h1 := heq e₀ he₀ f hf h a ha
      rw [ha₀', mul_inv_cancel_right] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1.symm)
  calc Nat.card A ≤ Nat.card ↥(A ⊓ centralizer ({e₀} : Set G)) ^ 2 :=
        card_le_card_inf_centralizer_sq_of_sq hAe (mem_normalizer_inf_centralizer (hER he₀))
          fun a _ => by rw [hE.2 e₀ he₀, one_mul, mul_one]
    _ ≤ _ := Nat.pow_le_pow_left (card_le_of_le hle) 2

theorem wGroup_eq_of_map_eq (hB : GWTwoBalanced G) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Open.fusionOddCore ↥P) (hU : Odd (Nat.card ρ.ker)) (hF : 16 ≤ Nat.card F)
    (hRP : R ≤ P) (hR2 : IsPGroup 2 R) (hRU : (R.subgroupOf P).map ρ = projUnitriangular 3 F)
    {t : G} (ht : orderOf t = 2) (htP : P ≤ centralizer ({t} : Set G)) (htnP : t ∉ P)
    {E : Subgroup G} (hE : IsElemTwo E) (hE8 : 8 ≤ Nat.card E)
    (hEt : E ≤ centralizer ({t} : Set G)) (hEP : E ≤ normalizer (P : Set G))
    (hER : E ≤ normalizer (R : Set G)) :
    wGroup E = wGroup (R ⊓ centralizer (R : Set G)) := by
  obtain ⟨hAe, hAc⟩ := isElemTwo_inf_centralizer_of_map_eq hU hRP hR2 hRU
  have hC0 := fun (E' : Subgroup G) (hE'e : IsElemTwo E') (hE'P : E' ≤ normalizer (P : Set G))
      (hE'R : E' ≤ normalizer (R : Set G)) =>
    card_le_card_inf_centralizer_sq_of_map_eq hρ hker hU hRP hR2 hRU hE'e hE'P hE'R
  generalize hAdef : R ⊓ centralizer (R : Set G) = A at hAe hAc hC0 ⊢
  have hAR : A ≤ R := hAdef ▸ inf_le_left
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  have hct : ∀ x ∈ E, x * t = t * x := fun x hx => mem_centralizer_singleton_iff.mp (hEt hx)
  have hcP : ∀ p ∈ P, p * t = t * p := fun p hp => mem_centralizer_singleton_iff.mp (htP hp)
  have htN : ∀ {K : Subgroup G}, K ≤ P → t ∈ normalizer (K : Set G) := fun hK =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun k hk => hcP k (hK hk))
  have hE'e : IsElemTwo (E ⊔ zpowers t) := hE.sup (isElemTwo_zpowers htt) fun x hx y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hct x hx) k).eq
  have hE'P : E ⊔ zpowers t ≤ normalizer (P : Set G) := sup_le hEP (zpowers_le.mpr (htN le_rfl))
  have hE'R : E ⊔ zpowers t ≤ normalizer (R : Set G) := sup_le hER (zpowers_le.mpr (htN hRP))
  have hC := hC0 _ hE'e hE'P hE'R
  generalize hE'def : E ⊔ zpowers t = E' at hE'e hC
  have hEE' : E ≤ E' := hE'def ▸ le_sup_left
  have htE' : t ∈ E' := hE'def ▸ mem_sup_right (mem_zpowers t)
  generalize hCdef : A ⊓ centralizer (E' : Set G) = C at hC
  have hCA : C ≤ A := hCdef ▸ inf_le_left
  have hCE' : C ≤ centralizer (E' : Set G) := hCdef ▸ inf_le_right
  have hC4 : 4 ≤ Nat.card C := by
    by_contra h
    push Not at h
    have : Nat.card C ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hB₀e : IsElemTwo (C ⊔ zpowers t) := (hAe.mono hCA).sup (isElemTwo_zpowers htt)
    fun x hx y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (hcP x (hRP (hAR (hCA hx)))) k).eq
  generalize hB₀def : C ⊔ zpowers t = B₀ at hB₀e
  have hCB₀ : C ≤ B₀ := hB₀def ▸ le_sup_left
  have htB₀ : t ∈ B₀ := hB₀def ▸ mem_sup_right (mem_zpowers t)
  have hB₀8 : 8 ≤ Nat.card B₀ := by
    have hne : Nat.card C ≠ Nat.card B₀ := fun h =>
      htnP (hRP (hAR (hCA ((eq_of_le_of_card_ge hCB₀ h.symm.le) ▸ htB₀))))
    obtain ⟨d, hd⟩ := card_dvd_of_le hCB₀
    have hd2 : 2 ≤ d := by
      rcases d with _ | _ | d
      · rw [mul_zero] at hd
        exact absurd hd Nat.card_pos.ne'
      · rw [zero_add, mul_one] at hd
        exact absurd hd.symm hne
      · omega
    nlinarith
  have hE3 : IsAbelianTwoOfRank 3 E := hE.isAbelianTwoOfRank hE8
  have hE'3 : IsAbelianTwoOfRank 3 E' := hE'e.isAbelianTwoOfRank (hE8.trans (card_le_of_le hEE'))
  have hB₀3 : IsAbelianTwoOfRank 3 B₀ := hB₀e.isAbelianTwoOfRank hB₀8
  have hA3 : IsAbelianTwoOfRank 3 A := hAe.isAbelianTwoOfRank (by omega)
  have hB₀E' : B₀ ≤ centralizer (E' : Set G) := hB₀def ▸ sup_le hCE'
    (zpowers_le.mpr (mem_centralizer_iff.mpr fun x hx => hE'e.1 x hx t htE'))
  have hB₀A : B₀ ≤ centralizer (A : Set G) := hB₀def ▸ sup_le
    (fun x hx => mem_centralizer_iff.mpr fun y hy => hAe.1 y hy x (hCA hx))
    (zpowers_le.mpr (mem_centralizer_iff.mpr fun x hx => hcP x (hRP (hAR hx))))
  rw [wGroup_eq_of_commute hB hE3 hE'3 fun x hx y hy => hE'e.1 x (hEE' hx) y hy,
    wGroup_eq_of_commute hB hE'3 hB₀3 fun x hx y hy => mem_centralizer_iff.mp (hB₀E' hy) x hx,
    wGroup_eq_of_commute hB hB₀3 hA3 fun x hx y hy => (mem_centralizer_iff.mp (hB₀A hx) y hy).symm]

end Gluing

theorem l34FieldSignalizerGluing_of_inputs (hmult : Quasithin.SchurMult2L3) :
    L34FieldSignalizerGluing := by
  intro G _ _ t P h
  have hB := gwTwoBalanced_of_l34FieldNormalSetting h
  have htnP := not_mem_of_l34FieldNormalSetting hmult h
  obtain ⟨-, ht, hPC, hcomp, hnorm, m, hm, -, hX⟩ := h
  have : Group.IsPerfect P := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hcomp
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPC).toMonoidHom)
      (subgroupOfEquivOfLe hPC).surjective
  have hZO := fusionZStar_eq_fusionOddCore_of_schurMult2L3 hmult (X := P) (by omega) hX
  obtain ⟨K, _, _, hK, ⟨ψ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK16 : 16 ≤ Nat.card K := by
    rw [hK]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  set ρ₀ : ↥P →* projectiveSL 3 K :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Open.fusionZStar ↥P)) with hρ₀def
  have hρ₀ : Function.Surjective ρ₀ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ρ₀.ker = Open.fusionOddCore ↥P := by
    rw [← hZO]
    ext x
    rw [MonoidHom.mem_ker, hρ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨R, hR, -⟩ := exists_isSylowTwoIn_ge (bot_le : ⊥ ≤ P) IsPGroup.of_bot
  have hR' : LargeExtraspecial.S5.IsSylowTwoIn (R.subgroupOf P) ⊤ :=
    ⟨le_top, hR.isPGroup.of_equiv (subgroupOfEquivOfLe hR.le).symm, by
      rw [relIndex_top_right]
      exact hR.not_dvd⟩
  have hS := hR'.map ρ₀
  rw [map_top_of_surjective ρ₀ hρ₀] at hS
  obtain ⟨S, hSU⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU' : LargeExtraspecial.S5.IsSylowTwoIn (projUnitriangular 3 K) ⊤ :=
    ⟨le_top, hSU ▸ S.isPGroup', by
      rw [relIndex_top_right, ← hSU]
      exact S.not_dvd_index⟩
  obtain ⟨c, -, hc⟩ := hS.exists_conj hU'
  set ρ : ↥P →* projectiveSL 3 K := (MulAut.conj c).toMonoidHom.comp ρ₀ with hρdef
  have hρ : Function.Surjective ρ := (MulAut.conj c).surjective.comp hρ₀
  have hker : ρ.ker = Open.fusionOddCore ↥P := by
    rw [← hker₀]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hRU : (R.subgroupOf P).map ρ = projUnitriangular 3 K := by
    ext y
    rw [hc y]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, by simp [hρdef, mul_assoc]⟩
    · rintro ⟨r, hr, hry⟩
      exact ⟨r, hr, by simp [hρdef, hry, mul_assoc]⟩
  have hU : Odd (Nat.card ρ.ker) := hker ▸ CGT.Timmesfeld75.odd_card_fusionOddCore ↥P
  have hR2 := hR.isPGroup
  have hRP := hR.le
  have hRG : GrSLit.IsSylowTwoIn R P := ⟨hRP, hR.toSylow, hR.coe_toSylow⟩
  obtain ⟨hAe, hAc⟩ := isElemTwo_inf_centralizer_of_map_eq hU hRP hR2 hRU
  have hPN := le_normalizer_wGroup_of_map_eq hB hρ hU hK16 hRP hR2 hRU
  refine ⟨wGroup (R ⊓ centralizer (R : Set G)), odd_card_wGroup hB hAe (hAc ▸ hK16), ?_, ?_⟩
  · intro g hg
    have hgP : R.map (MulAut.conj g).toMonoidHom ≤ P := by
      rintro _ ⟨r, hr, rfl⟩
      exact (mem_normalizer_iff.mp hg r).mp (hRP hr)
    obtain ⟨d, hdP, hd⟩ := GrSLit.IsSylowTwoIn.exists_conj_le hRG hgP (hR2.map _)
    have hdg : R.map (MulAut.conj (d * g)).toMonoidHom = R := by
      refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj _).injective])
      rintro _ ⟨r, hr, rfl⟩
      have := hd _ ⟨r, hr, rfl⟩
      convert this using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      group
    have := mul_mem (inv_mem (hPN hdP)) (GrS4.mem_normalizer_wGroup
      (mem_normalizer_inf_centralizer (mem_normalizer_iff_map_conj_eq.mpr hdg)))
    simpa using this
  · intro E hEt hEab hE8
    have hE : IsElemTwo E := by
      refine ⟨fun a ha b hb => congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
        fun a ha => ?_⟩
      rw [← pow_two]
      exact hEab.2 a ha
    have hCN : centralizer ({t} : Set G) ≤ normalizer (P : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hPC).mp hnorm
    obtain ⟨D, hD, hED, -⟩ :=
      HSFLit.L34Inv.exists_isSylowTwoIn_normalized hE.isPGroup (hEt.trans hCN)
    obtain ⟨d, hdP, hd⟩ := GrSLit.IsSylowTwoIn.exists_conj_le hRG hD.1
      (GrSLit.IsSylowTwoIn.isPGroup hD)
    have hDR : D.map (MulAut.conj d).toMonoidHom = R := by
      refine eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hd x hx
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨hDP, Q', hQ'⟩ := hD
        rw [card_map_of_injective (MulAut.conj d).injective, hR.card_eq,
          Nat.card_congr ((subgroupOfEquivOfLe hDP).symm.toEquiv.trans
            (MulEquiv.subgroupCongr hQ'.symm).toEquiv), Sylow.card_eq_multiplicity]
    have hmemR : ∀ h : G, h ∈ R ↔ d⁻¹ * h * d ∈ D := fun h => by
      rw [← hDR]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [mul_assoc] using hy
      · intro hh
        exact ⟨_, hh, by simp [mul_assoc]⟩
    have hdt : d * t * d⁻¹ = t :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hPC hdP))
    have hE₁t : E.map (MulAut.conj d).toMonoidHom ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hxt := mem_centralizer_singleton_iff.mp (hEt hx)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc d * x * d⁻¹ * t = d * x * d⁻¹ * (d * t * d⁻¹) := by rw [hdt]
        _ = d * (x * t) * d⁻¹ := by group
        _ = d * (t * x) * d⁻¹ := by rw [hxt]
        _ = d * t * d⁻¹ * (d * x * d⁻¹) := by group
        _ = t * (d * x * d⁻¹) := by rw [hdt]
    have hE₁R : E.map (MulAut.conj d).toMonoidHom ≤ normalizer (R : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      refine mem_normalizer_iff.mpr fun h => ?_
      rw [hmemR, hmemR]
      have e : d⁻¹ * ((MulAut.conj d).toMonoidHom x * h * ((MulAut.conj d).toMonoidHom x)⁻¹) * d =
          x * (d⁻¹ * h * d) * x⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact mem_normalizer_iff.mp (hED hx) _
    have hE₁8 : 8 ≤ Nat.card (E.map (MulAut.conj d).toMonoidHom) := by
      rw [card_map_of_injective (MulAut.conj d).injective]
      exact hE8
    have hW1 := wGroup_eq_of_map_eq hB hρ hker hU hK16 hRP hR2 hRU ht hPC htnP (hE.map_conj d)
      hE₁8 hE₁t (hE₁t.trans hCN) hE₁R
    rw [wGroup_map_conj] at hW1
    exact map_injective (MulAut.conj d).injective
      (hW1.trans (mem_normalizer_iff_map_conj_eq.mp (hPN hdP)).symm)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
