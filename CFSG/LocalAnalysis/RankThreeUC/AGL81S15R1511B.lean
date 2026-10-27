module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSimple

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open scoped commutatorElement

section LiftLevel

open KFactsPair

variable {X : Type} [Group X] [Finite X]

theorem three_dvd_card_add_one {Q : TauCeti.PrimePower} (hp : Q.p = 2) (hn : Odd Q.exponent) :
    3 ∣ Q.card + 1 := by
  obtain ⟨k, hk⟩ := hn
  rw [TauCeti.PrimePower.card_def, hp, hk, pow_succ, pow_mul]
  have h : (2 ^ 2) ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem pElement_le_lift_aux1 {L C : Subgroup X} [L.Normal] [C.Normal] (hC : ¬ 3 ∣ Nat.card C)
    {x : X} (hx : x ∈ L ⊔ C) {k : ℕ} (hk : orderOf x = 3 ^ k) : x ∈ L := by
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  have h1 : orderOf (QuotientGroup.mk' L (l * c)) ∣ 3 ^ k := hk ▸ orderOf_map_dvd _ _
  have hl1 : QuotientGroup.mk' L l = 1 := (QuotientGroup.eq_one_iff l).2 hl
  have h2 : QuotientGroup.mk' L (l * c) = QuotientGroup.mk' L c := by
    rw [map_mul, hl1, one_mul]
  have h3 : orderOf (QuotientGroup.mk' L (l * c)) ∣ Nat.card C := by
    rw [h2]
    refine (orderOf_map_dvd _ _).trans ?_
    rw [← Subgroup.orderOf_mk c hc]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card C) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC)
  have h4 : orderOf (QuotientGroup.mk' L (l * c)) = 1 :=
    Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h3)
  exact (QuotientGroup.eq_one_iff (l * c)).1 (orderOf_eq_one_iff.1 h4)

theorem pElement_le_lift {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hnorm : Ls.Normal) (hL : LiftOf T L Ls)
    (hC : ¬ 3 ∣ Nat.card (gnC T))
    (hle : pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls.comap (toStar T)) :
    L.Normal ∧ pElementSubgroup 3 (⊤ : Subgroup X) ≤ L := by
  haveI := hnorm
  have hLn : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : toStar T g ∈ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have h1 := liftOf_conj hX hLs hL g hg
    have h2 : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [h1] at h2
  refine ⟨hLn, ?_⟩
  have hcomap := (liftOf_central_ext hX hLs hL).2
  refine (Subgroup.closure_le L).2 ?_
  rintro x ⟨-, k, hk⟩
  have hx : x ∈ Ls.comap (toStar T) :=
    hle (Subgroup.subset_closure ⟨Subgroup.mem_top x, k, hk⟩)
  rw [hcomap] at hx
  haveI := hLn
  exact pElement_le_lift_aux1 hC hx hk

theorem lift_inf_gnC_le_pCore_of_U4_aux1 {K S : Type*} [Group K] [Group S] (f : K →* S)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hS : Subgroup.center S = ⊥) : f.ker = Subgroup.center K := by
  refine le_antisymm hker ?_
  intro z hz
  rw [MonoidHom.mem_ker]
  have h : f z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨k, rfl⟩ := hf s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
  rw [hS, Subgroup.mem_bot] at h
  exact h

theorem lift_inf_gnC_le_pCore_of_U4_aux2 {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hd : d.1 = .twistedA 3 Q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : Subgroup.center S = ⊥ := by
  haveI hs : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group :=
    CFSG.LocalAnalysis.RankThreeUC.u4Group_isSimple hQ hd
  haveI : IsSimpleGroup S := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.RankThreeUC.u4Group_nonabelian hQ hd
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    apply hab
    have h1 : e.symm a * e.symm b = e.symm b * e.symm a := by
      have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top (e.symm a)) (e.symm b)
      exact this.symm
    have h2 := congrArg e h1
    simpa using h2

theorem lift_inf_gnC_le_pCore_of_U4 (hKSMU4 : KSMU4) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (hU : IsUFourOdd ↥Ls) : L ⊓ gnC T ≤ CFSG.pCore 2 X := by
  obtain ⟨d, Q, hQ2, -, hd, ⟨e⟩⟩ := hU
  let φ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hX)
  have hφ : ∀ A : Subgroup X, (barO2 A).map φ = A.map (toStar T) := by
    intro A
    unfold barO2
    rw [Subgroup.map_map]
    congr 1
  have hφmk : ∀ x : X, φ (QuotientGroup.mk' (CFSG.pCore 2 X) x) = toStar T x := fun x => rfl
  let f : ↥(barO2 L) →* ↥Ls := (φ.comp (barO2 L).subtype).codRestrict Ls (by
    intro k
    have h : φ k ∈ (barO2 L).map φ := ⟨k, k.2, rfl⟩
    rw [hφ, hL.2] at h
    exact h)
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    rw [← hL.2, ← hφ] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨⟨k, hk⟩, rfl⟩
  have hcentral := (liftOf_central_ext hX hLs hL).1
  have hkerf : f.ker ≤ Subgroup.center ↥(barO2 L) := by
    intro k hk
    obtain ⟨l, hl, hlk⟩ := k.2
    have h1 : φ k = 1 := by
      have h0 : f k = 1 := MonoidHom.mem_ker.1 hk
      exact congrArg Subtype.val h0
    have h2 : l ∈ gnC T := by
      have h3 : toStar T l = 1 := by
        rw [← hφmk l]
        have : QuotientGroup.mk' (CFSG.pCore 2 X) l = (k : X ⧸ CFSG.pCore 2 X) := hlk
        rw [this]
        exact h1
      exact (QuotientGroup.eq_one_iff l).1 h3
    have h4 : (k : X ⧸ CFSG.pCore 2 X) ∈
        ((L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
      ⟨l, ⟨hl, h2⟩, hlk⟩
    obtain ⟨z, hz, hzk⟩ := hcentral h4
    have : z = k := Subtype.ext hzk
    rwa [← this]
  have hker_eq : f.ker = Subgroup.center ↥(barO2 L) :=
    lift_inf_gnC_le_pCore_of_U4_aux1 f hf hkerf (lift_inf_gnC_le_pCore_of_U4_aux2 hQ2 hd e)
  let eK : (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans e
  have hcard : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
    hKSMU4 ↥(barO2 L) hL.1.component.2.2 d ⟨Q, hQ2, hd⟩ ⟨eK⟩ (centre_barO2_odd hL.1)
  have hbot : Subgroup.center ↥(barO2 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  intro x hx
  have h1 := hcentral ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem pElement_quot_equiv_aux1 {Y : Type*} [Group Y] (p : ℕ) :
    (pElementSubgroup p (⊤ : Subgroup Y)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold pElementSubgroup at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top _, ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    refine ⟨k, ?_⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [MulAut.conj_apply, hk] using this
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem pElement_quot_equiv_aux2 {D : Subgroup X} (hD : D.Normal) :
    (CFSG.pCore 2 ↥D).map D.subtype ≤ CFSG.pCore 2 X := by
  haveI := hD
  have hPp : IsPGroup 2 ↥((CFSG.pCore 2 ↥D).map D.subtype) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥D)) D.subtype
  haveI hPnorm : ((CFSG.pCore 2 ↥D).map D.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨n', hn', rfl⟩ := hn
    refine ⟨MulAut.conjNormal g n', ?_, MulAut.conjNormal_apply g n'⟩
    have hchar : (CFSG.pCore 2 ↥D).Characteristic := inferInstance
    have h1 : MulAut.conjNormal g n' ∈ (CFSG.pCore 2 ↥D).map (MulAut.conjNormal g).toMonoidHom :=
      ⟨n', hn', rfl⟩
    rwa [Subgroup.characteristic_iff_map_eq.1 hchar (MulAut.conjNormal g)] at h1
  exact isC2_normalizer_aux0 hPp

theorem pElement_quot_equiv {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hnorm : Ls.Normal) (hL : LiftOf T L Ls)
    (hC : ¬ 3 ∣ Nat.card (gnC T))
    (hle : pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hy : ¬ pElementSubgroup 3 Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (hker : L ⊓ gnC T ≤ CFSG.pCore 2 X) :
    Nonempty ((↥(pElementSubgroup 3 (⊤ : Subgroup X)) ⧸
      CFSG.pCore 2 ↥(pElementSubgroup 3 (⊤ : Subgroup X))) ≃* ↥Ls) := by
  have hDn : (pElementSubgroup 3 (⊤ : Subgroup X)).Normal := pElement_quot_equiv_aux1 3
  obtain ⟨-, hDL⟩ := pElement_le_lift hX hLs hnorm hL hC hle
  set D := pElementSubgroup 3 (⊤ : Subgroup X) with hD
  let ψ : ↥D →* ↥Ls := ((toStar T).comp D.subtype).codRestrict Ls (fun d => hle d.2)
  have hLsD : Ls ≤ D.map (toStar T) := by
    have hA11 := pElementSubgroup_eq_of_isComponent hLs hy
    refine hA11.symm.le.trans ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨-, k, hk⟩
    obtain ⟨u, hu, m, hm⟩ := exists_pPow_lift (toStar T) (QuotientGroup.mk'_surjective _)
      Nat.prime_three ⟨k, hk⟩
    exact ⟨u, Subgroup.subset_closure ⟨Subgroup.mem_top u, m, hm⟩, hu⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨s, hs⟩
    obtain ⟨d, hd, hds⟩ := hLsD hs
    exact ⟨⟨d, hd⟩, Subtype.ext hds⟩
  have hker' : ψ.ker = CFSG.pCore 2 ↥D := by
    refine le_antisymm ?_ ?_
    · intro d hd
      have h1 : toStar T d = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
      have h2 : (d : X) ∈ gnC T := (QuotientGroup.eq_one_iff (d : X)).1 h1
      have h3 : (d : X) ∈ CFSG.pCore 2 X := hker ⟨hDL d.2, h2⟩
      haveI : ((CFSG.pCore 2 X).subgroupOf D).Normal :=
        Subgroup.Normal.subgroupOf CFSG.pCore_normal D
      have hN2 : IsPGroup 2 ↥((CFSG.pCore 2 X).subgroupOf D) :=
        (CFSG.pCore_isPGroup (p := 2) (G := X)).comap_subtype
      exact isC2_normalizer_aux0 hN2 (Subgroup.mem_subgroupOf.2 h3)
    · intro d hd
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h1 : (d : X) ∈ CFSG.pCore 2 X := pElement_quot_equiv_aux2 hDn ⟨d, hd, rfl⟩
      have h2 : (d : X) ∈ gnC T := pCore_le_gnC hX h1
      exact (QuotientGroup.eq_one_iff (d : X)).2 h2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem u4Data_of_lift (hKSMU4 : KSMU4) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hnorm : Ls.Normal) (hL : LiftOf T L Ls)
    (hC : ¬ 3 ∣ Nat.card (gnC T))
    (hle : pElementSubgroup 3 (⊤ : Subgroup X) ≤ Ls.comap (toStar T))
    (hy : ¬ pElementSubgroup 3 Ls ≤ (Subgroup.center ↥Ls).map Ls.subtype)
    (hU : IsUFourOdd ↥Ls) : U4Data X := by
  unfold U4Data
  obtain ⟨d, Q, hQ2, hQodd, hd, ⟨e⟩⟩ := hU
  have hker := lift_inf_gnC_le_pCore_of_U4 hKSMU4 hX hLs hL ⟨d, Q, hQ2, hQodd, hd, ⟨e⟩⟩
  obtain ⟨φ⟩ := pElement_quot_equiv hX hLs hnorm hL hC hle hy hker
  exact ⟨d, ⟨Q, hQ2, hd, three_dvd_card_add_one hQ2 hQodd⟩, ⟨φ.trans e⟩⟩

theorem u4Shape_of_u4Data_aux1 {G : Type} [Group G] (M : Subgroup G) :
    (pElementSubgroup 3 (⊤ : Subgroup ↥M)).map M.subtype =
      CFSG.RankThree.PartOne.pElementSubgroup 3 M := by
  unfold pElementSubgroup CFSG.RankThree.PartOne.pElementSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨-, k, hk⟩, rfl⟩
    exact ⟨x.2, k, by rw [← hk]; exact Subgroup.orderOf_coe x⟩
  · rintro ⟨hyM, k, hk⟩
    exact ⟨⟨y, hyM⟩, ⟨Subgroup.mem_top _, k, by rw [← hk]; exact Subgroup.orderOf_mk y hyM⟩, rfl⟩

theorem u4Shape_of_u4Data {G : Type} [Group G] [Finite G] (M : Subgroup G) (h : U4Data ↥M) :
    U4Shape 3 M := by
  unfold U4Data at h
  unfold U4Shape
  obtain ⟨d, hdq, ⟨φ⟩⟩ := h
  refine ⟨d, hdq, ?_⟩
  let DX : Subgroup ↥M := pElementSubgroup 3 (⊤ : Subgroup ↥M)
  let e : ↥DX ≃* ↥(CFSG.RankThree.PartOne.pElementSubgroup 3 M) :=
    (DX.equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr (u4Shape_of_u4Data_aux1 M))
  have hc : (CFSG.pCore 2 ↥DX).map e.toMonoidHom =
      CFSG.pCore 2 ↥(CFSG.RankThree.PartOne.pElementSubgroup 3 M) := CFSG.pCore_map_iso 2 e
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥DX)
    (CFSG.pCore 2 ↥(CFSG.RankThree.PartOne.pElementSubgroup 3 M)) e hc).symm.trans φ⟩

end LiftLevel

end CFSG.LocalAnalysis.RankThreeUC.S15
