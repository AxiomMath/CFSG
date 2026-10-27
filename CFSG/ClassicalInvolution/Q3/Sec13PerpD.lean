module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpW
import CFSG.ClassicalInvolution.Q3.Q3CLWylA

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem perpD_comm_trans_of_not_conn {Q : Type*} [Group Q] {Δ : Set Q}
    (h : Star3T.IsTT Δ) (hS : Star3T.IsStar Δ) {p q : Q} (hp : p ∈ Δ) (hq : q ∈ Δ)
    (hpq : ¬ Star3T.Conn Δ p q) {x y z : Q} (hx : x ∈ Δ) (hy : y ∈ Δ) (hz : z ∈ Δ)
    (hxy : x * y = y * x) (hyz : y * z = z * y) : x * z = z * x := by
  have hpl : Star3T.IsPlane Δ p q (p * q * p) := ⟨hp, hq, hpq, rfl⟩
  have hr : p * q * p ∈ Δ := h.mem_third hpl
  have hnpr : ¬ Star3T.Conn Δ p (p * q * p) := h.not_conn_third_left hpl
  have hnqr : ¬ Star3T.Conn Δ q (p * q * p) := h.not_conn_third_right hpl
  have hnqp : ¬ Star3T.Conn Δ q p := fun c => hpq c.symm
  have hnrp : ¬ Star3T.Conn Δ (p * q * p) p := fun c => hnpr c.symm
  have hnrq : ¬ Star3T.Conn Δ (p * q * p) q := fun c => hnqr c.symm
  have hU := Star3T.IsTT.cent_union_eq hS hpl
  have hcov : ∀ v ∈ Δ, v ∈ Star3T.cent Δ p ∨ v ∈ Star3T.cent Δ q ∨
      v ∈ Star3T.cent Δ (p * q * p) := by
    intro v hv
    have hv' := hv
    rw [hU, Set.mem_union, Set.mem_union] at hv'
    tauto
  have hcovQ : ∀ v ∈ Δ, v ∈ Star3T.cent Δ q ∨ v ∈ Star3T.cent Δ p ∨
      v ∈ Star3T.cent Δ (p * q * p) := fun v hv => by
    have := hcov v hv
    tauto
  have hcovR : ∀ v ∈ Δ, v ∈ Star3T.cent Δ (p * q * p) ∨ v ∈ Star3T.cent Δ p ∨
      v ∈ Star3T.cent Δ q := fun v hv => by
    have := hcov v hv
    tauto
  have cross : ∀ {a b u v : Q}, a ∈ Δ → b ∈ Δ → ¬ Star3T.Conn Δ a b →
      u ∈ Star3T.cent Δ a → v ∈ Star3T.cent Δ b → u * v ≠ v * u :=
    fun ha hb hab hu hv e => hab ((Star3T.conn_of_mem_cent ha hu).trans
      ((Star3T.conn_of_commute hu.1 hv.1 e).trans (Star3T.conn_of_mem_cent hb hv).symm))
  have closed : ∀ {a b c : Q}, a ∈ Δ → b ∈ Δ → c ∈ Δ → ¬ Star3T.Conn Δ a b →
      ¬ Star3T.Conn Δ a c → (∀ v ∈ Δ, v ∈ Star3T.cent Δ a ∨ v ∈ Star3T.cent Δ b ∨
        v ∈ Star3T.cent Δ c) → ∀ {u v : Q}, u ∈ Star3T.cent Δ a → v ∈ Δ →
        u * v = v * u → v ∈ Star3T.cent Δ a := by
    intro a b c ha hb hc hab hac hcov' u v hu hv e
    rcases hcov' v hv with h1 | h1 | h1
    · exact h1
    · exact absurd e (cross ha hb hab hu h1)
    · exact absurd e (cross ha hc hac hu h1)
  have clP : ∀ {u v : Q}, u ∈ Star3T.cent Δ p → v ∈ Star3T.cent Δ p → u * v = v * u :=
    fun hu hv => h.isClique_cent hS hp hq hpq hu hv
  have clQ : ∀ {u v : Q}, u ∈ Star3T.cent Δ q → v ∈ Star3T.cent Δ q → u * v = v * u :=
    fun hu hv => h.isClique_cent hS hq hp hnqp hu hv
  have clR : ∀ {u v : Q}, u ∈ Star3T.cent Δ (p * q * p) → v ∈ Star3T.cent Δ (p * q * p) →
      u * v = v * u := fun hu hv => h.isClique_cent hS hr hp hnrp hu hv
  rcases hcov y hy with hy1 | hy1 | hy1
  · exact clP (closed hp hq hr hpq hnpr hcov hy1 hx hxy.symm)
      (closed hp hq hr hpq hnpr hcov hy1 hz hyz)
  · exact clQ (closed hq hp hr hnqp hnqr hcovQ hy1 hx hxy.symm)
      (closed hq hp hr hnqp hnqr hcovQ hy1 hz hyz)
  · exact clR (closed hr hp hq hnrp hnrq hcovR hy1 hx hxy.symm)
      (closed hr hp hq hnrp hnrq hcovR hy1 hz hyz)

private theorem perpD_partIHypG (h : EndHyp Ω) : Q3CL.PartIHypG Ω :=
  ⟨h.thmD.hyp, classicalClause_of_two h.thmD.hyp h.thmD.two, h.thmD.aEmpty⟩

private theorem perpD_muDelta_comm_trans (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {x y z : ↥(muGroup Ω W)} (hx : x ∈ Thompson.muDelta Ω W) (hy : y ∈ Thompson.muDelta Ω W)
    (hz : z ∈ Thompson.muDelta Ω W) (hxy : x * y = y * x) (hyz : y * z = z * y) :
    x * z = z * x := by
  have hP := perpD_partIHypG h
  obtain ⟨a, ha, hxa⟩ := Q3CL.Wyl.exists_not_conn_at hP hW (h.not_dbarConnected hW) x
  exact perpD_comm_trans_of_not_conn (Q3T6.Mu.isTT_muDelta hP hW)
    (Q3T6.Mu.isStar_muDelta (Q3CL.T8.ctxOf hP hW)) hx ha hxa hx hy hz hxy hyz

private theorem perpD_exists_rep (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R : Subgroup G} (hR : R ∈ DSet Ω W) : ∃ ρ : Thompson.Rep Ω W, ρ.K = R := by
  obtain ⟨hRΩ, -⟩ := h.mem_dSet_iff.mp hR
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D h.thmD.hyp hW hR
  have hRR : IsSylow2In R R :=
    ⟨le_rfl, h.thmD.two R hRΩ, fun _ hVR _ hRV => le_antisymm hVR hRV⟩
  exact ⟨⟨R, R, r, hRΩ, hR, hRR, hr, hrW⟩, rfl⟩

private theorem perpD_rep_K_mem (h : EndHyp Ω) {W : Subgroup G} (ρ : Thompson.Rep Ω W) :
    ρ.K ∈ DSet Ω W := by
  have hRK : ρ.R = ρ.K :=
    (ρ.hRK.2.2 ρ.K le_rfl (h.thmD.two ρ.K ρ.hK) ρ.hRK.1).symm
  rw [← hRK]
  exact ρ.hR

private theorem perpD_mem_KPerp_iff {R T : Subgroup G} :
    T ∈ KPerp Ω R ↔ T = R ∨ T ∈ omegaNbr Ω R :=
  Iff.rfl

private theorem perpD_ncard_eq (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R : Subgroup G} (hR : R ∈ DSet Ω W) (ρ : Thompson.Rep Ω W) (hρ : ρ.K = R) :
    (KPerp Ω R ∩ DSet Ω W).ncard =
      (Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρ)).ncard := by
  have hP := perpD_partIHypG h
  have hrep : ∀ T ∈ DSet Ω W, ∃ σ : Thompson.Rep Ω W, σ.K = T :=
    fun T hT => perpD_exists_rep h hW hT
  have : Nonempty (Thompson.Rep Ω W) := ⟨ρ⟩
  choose! rep hrep using hrep
  obtain ⟨f, hf⟩ : ∃ f : Subgroup G → ↥(muGroup Ω W),
      ∀ T, f T = MuTab.muTabElt (rep T) := ⟨_, fun _ => rfl⟩
  have hRρ : MuTab.muTabElt (rep R) = MuTab.muTabElt ρ :=
    (Q3T6.Mu.muTabElt_eq_iff hP hW _ _).mpr (by rw [hrep R hR, hρ])
  have hfR : f R = MuTab.muTabElt ρ := by rw [hf, hRρ]
  have hinj : Set.InjOn f (KPerp Ω R ∩ DSet Ω W) := by
    intro T hT T' hT' hTT'
    rw [hf, hf] at hTT'
    have e := (Q3T6.Mu.muTabElt_eq_iff hP hW (rep T) (rep T')).mp hTT'
    rw [hrep T hT.2, hrep T' hT'.2] at e
    exact e
  have himg : f '' (KPerp Ω R ∩ DSet Ω W) =
      Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρ) := by
    ext x
    constructor
    · rintro ⟨T, ⟨hTp, hTD⟩, rfl⟩
      refine ⟨by rw [hf]; exact MuTab.muTabElt_mem (rep T), ?_⟩
      rw [← hfR]
      by_cases hTR : T = R
      · rw [hTR]
      · have hTn : T ∈ omegaNbr Ω R := (perpD_mem_KPerp_iff.mp hTp).resolve_left hTR
        have hne : (rep R).K ≠ (rep T).K := by
          rw [hrep R hR, hrep T hTD]
          exact fun e => hTR e.symm
        have hc : MuTab.muTabElt (rep R) * MuTab.muTabElt (rep T) =
            MuTab.muTabElt (rep T) * MuTab.muTabElt (rep R) :=
          (Q3T6.Mu.muTab_commute_iff hP hW (rep R) (rep T) hne).mpr
            (by rw [hrep R hR, hrep T hTD]; exact hTn)
        rw [hf, hf]
        exact hc.symm
    · rintro ⟨hxΔ, hx⟩
      obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hxΔ
      have hσD : σ.K ∈ DSet Ω W := perpD_rep_K_mem h σ
      refine ⟨σ.K, ⟨?_, hσD⟩, ?_⟩
      · by_cases hσR : σ.K = R
        · exact perpD_mem_KPerp_iff.mpr (Or.inl hσR)
        · refine perpD_mem_KPerp_iff.mpr (Or.inr ?_)
          have hne : (rep R).K ≠ σ.K := by
            rw [hrep R hR]
            exact fun e => hσR e.symm
          have hcomm : MuTab.muTabElt (rep R) * MuTab.muTabElt σ =
              MuTab.muTabElt σ * MuTab.muTabElt (rep R) := by
            rw [hRρ]
            exact hx.symm
          have := (Q3T6.Mu.muTab_commute_iff hP hW (rep R) σ hne).mp hcomm
          rw [hrep R hR] at this
          exact this
      · rw [hf]
        exact (Q3T6.Mu.muTabElt_eq_iff hP hW _ _).mpr (hrep σ.K hσD)
  rw [← himg]
  exact hinj.ncard_image.symm

private theorem perpD_not_S3_and_S4 {W : Subgroup G} (h3 : MuIsoS3 Ω W) (h4 : MuIsoS4 Ω W) :
    False := by
  obtain ⟨e3⟩ := h3
  obtain ⟨e4⟩ := h4
  have c3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    rfl
  have c4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
    rfl
  have h1 := Nat.card_congr e3.toEquiv
  have h2 := Nat.card_congr e4.toEquiv
  omega

theorem dSet_comm_trans (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R T U : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hU : U ∈ DSet Ω W)
    (hRT : T ∈ KPerp Ω R) (hTU : U ∈ KPerp Ω T) : U ∈ KPerp Ω R := by
  obtain ⟨ρR, hρR⟩ := perpD_exists_rep h hW hR
  obtain ⟨ρT, hρT⟩ := perpD_exists_rep h hW hT
  obtain ⟨ρU, hρU⟩ := perpD_exists_rep h hW hU
  have hP := perpD_partIHypG h
  by_cases hUR : U = R
  · exact perpD_mem_KPerp_iff.mpr (Or.inl hUR)
  by_cases hTR : T = R
  · rw [hTR] at hTU
    exact hTU
  have hTn : T ∈ omegaNbr Ω R := (perpD_mem_KPerp_iff.mp hRT).resolve_left hTR
  by_cases hUT : U = T
  · rw [hUT]
    exact hRT
  have hUn : U ∈ omegaNbr Ω T := (perpD_mem_KPerp_iff.mp hTU).resolve_left hUT
  have hc1 : MuTab.muTabElt ρR * MuTab.muTabElt ρT = MuTab.muTabElt ρT * MuTab.muTabElt ρR :=
    (Q3T6.Mu.muTab_commute_iff hP hW ρR ρT (by rw [hρR, hρT]; exact Ne.symm hTR)).mpr
      (by rw [hρR, hρT]; exact hTn)
  have hc2 : MuTab.muTabElt ρT * MuTab.muTabElt ρU = MuTab.muTabElt ρU * MuTab.muTabElt ρT :=
    (Q3T6.Mu.muTab_commute_iff hP hW ρT ρU (by rw [hρT, hρU]; exact Ne.symm hUT)).mpr
      (by rw [hρT, hρU]; exact hUn)
  have hc3 := perpD_muDelta_comm_trans h hW (MuTab.muTabElt_mem ρR) (MuTab.muTabElt_mem ρT)
    (MuTab.muTabElt_mem ρU) hc1 hc2
  have hnb : ρU.K ∈ omegaNbr Ω ρR.K :=
    (Q3T6.Mu.muTab_commute_iff hP hW ρR ρU (by rw [hρR, hρU]; exact Ne.symm hUR)).mp hc3
  rw [hρR, hρU] at hnb
  exact perpD_mem_KPerp_iff.mpr (Or.inr hnb)

theorem dSet_class_ncard (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    (MuIsoS3 Ω W → (KPerp Ω R ∩ DSet Ω W).ncard = 1) ∧
    (MuIsoS4 Ω W → (KPerp Ω R ∩ DSet Ω W).ncard = 2) ∧
    (MuIsoWylD4 Ω W → (KPerp Ω R ∩ DSet Ω W).ncard = 4) := by
  obtain ⟨ρ, hρ⟩ := perpD_exists_rep h hW hR
  have hP := perpD_partIHypG h
  have hnc := h.not_dbarConnected hW
  have hcl := Q3CL.Wyl.muIso_of_cent hP hW hnc ρ
  have hk := Q3T8.Asc77.thompsonClique G Ω h.partIHyp W hW hnc (MuTab.muTabElt ρ)
    (MuTab.muTabElt_mem ρ)
  rw [perpD_ncard_eq h hW hR ρ hρ]
  refine ⟨fun h3 => ?_, fun h4 => ?_, fun hw => ?_⟩
  · rcases hk with hk | hk | ⟨hk, -⟩
    · exact hk
    · exact (perpD_not_S3_and_S4 h3 (hcl.2.1 hk)).elim
    · exact ((Q3CL.Wyl.not_muIsoS3_or_S4 (hcl.2.2 hk)).1 h3).elim
  · rcases hk with hk | hk | ⟨hk, -⟩
    · exact (perpD_not_S3_and_S4 (hcl.1 hk) h4).elim
    · exact hk
    · exact ((Q3CL.Wyl.not_muIsoS3_or_S4 (hcl.2.2 hk)).2 h4).elim
  · rcases hk with hk | hk | ⟨hk, -⟩
    · exact ((Q3CL.Wyl.not_muIsoS3_or_S4 hw).1 (hcl.1 hk)).elim
    · exact ((Q3CL.Wyl.not_muIsoS3_or_S4 hw).2 (hcl.2.1 hk)).elim
    · exact hk

private theorem perpD_isPGroup_sup_finset {C : Set (Subgroup G)}
    (h2 : ∀ T ∈ C, IsPGroup 2 (T : Subgroup G))
    (hcomm : ∀ R ∈ C, ∀ T ∈ C, R ≠ T → ∀ x ∈ R, ∀ y ∈ T, x * y = y * x) :
    ∀ F : Finset (Subgroup G), (∀ T ∈ F, T ∈ C) → IsPGroup 2 (F.sup id : Subgroup G) := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.sup_empty]
    exact IsPGroup.of_bot
  | @insert R F hRF ih =>
    intro hF
    have hRC : R ∈ C := hF R (Finset.mem_insert_self R F)
    have hFC : ∀ T ∈ F, T ∈ C := fun T hT => hF T (Finset.mem_insert_of_mem hT)
    have hN : F.sup id ≤ Subgroup.normalizer (R : Set G) := Finset.sup_le fun T hT => by
      have hTR : T ≠ R := fun e => hRF (e ▸ hT)
      exact Asc77.AscL62.le_normalizer_of_commutes (hcomm T (hFC T hT) R hRC hTR)
    rw [Finset.sup_insert]
    exact IsPGroup.to_sup_of_normal_left' (h2 R hRC) (ih hFC) hN

private theorem perpD_le_normalizer_of_invariant {S : Subgroup G} {η : Set (Subgroup G)}
    (hinv : ∀ s ∈ S, ∀ V ∈ η, conjSub s V ∈ η) :
    S ≤ Subgroup.normalizer ((⨆ V ∈ η, V : Subgroup G) : Set G) := by
  have hle : ∀ s ∈ S, conjSub s (⨆ V ∈ η, V) ≤ ⨆ V ∈ η, V := fun s hs =>
    Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun V hV =>
      Subgroup.map_le_iff_le_comap.mp (le_iSup₂_of_le (conjSub s V) (hinv s hs V hV) le_rfl))
  refine fun s hs => mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (hle s hs) ?_)
  have h := conjSub_mono (n := s) (hle s⁻¹ (inv_mem hs))
  rwa [conjSub_conjSub_inv] at h

private theorem perpD_exists_wSet (h : EndHyp Ω) {C : Set (Subgroup G)} (hC : C ⊆ Ω)
    (hcomm : ∀ R ∈ C, ∀ T ∈ C, R ≠ T → ∀ x ∈ R, ∀ y ∈ T, x * y = y * x) :
    ∃ W' ∈ WSet Ω, C ⊆ DSet Ω W' := by
  classical
  have h2 : ∀ T ∈ C, IsPGroup 2 (T : Subgroup G) := fun T hT => h.thmD.two T (hC hT)
  have hfin : C.Finite := Set.toFinite C
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (perpD_isPGroup_sup_finset h2 hcomm hfin.toFinset
    fun T hT => (Set.Finite.mem_toFinset hfin).mp hT)
  have hCS : ∀ R ∈ C, R ≤ (S : Subgroup G) := fun R hR =>
    (Finset.le_sup (f := id) ((Set.Finite.mem_toFinset hfin).mpr hR)).trans hS
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet h.thmD.hyp S
  refine ⟨⨆ V ∈ η, V, ⟨η, ⟨S, hηS, hinv⟩, rfl⟩, fun R hR => ?_⟩
  exact h.mem_dSet_iff.mpr ⟨hC hR, (hCS R hR).trans (perpD_le_normalizer_of_invariant hinv)⟩

private theorem perpD_clique_sub_kPerp (h : EndHyp Ω) {C : Set (Subgroup G)} (hC : C ⊆ Ω)
    (hcomm : ∀ R ∈ C, ∀ T ∈ C, R ≠ T → ∀ x ∈ R, ∀ y ∈ T, x * y = y * x) {R : Subgroup G}
    (hR : R ∈ C) : C ⊆ KPerp Ω R := by
  intro T hT
  rw [perpD_mem_KPerp_iff]
  by_cases hTR : T = R
  · exact Or.inl hTR
  · refine Or.inr ((TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two).mpr ⟨hC hT, hTR, ?_⟩)
    exact Asc77.AscL62.le_normalizer_of_commutes (hcomm T hT R hR hTR)

private theorem perpD_le_normalizer_conj_iff (g : G) (X V : Subgroup G) :
    X ≤ Subgroup.normalizer ((conjSub g V : Subgroup G) : Set G) ↔
      conjSub g⁻¹ X ≤ Subgroup.normalizer (V : Set G) := by
  rw [← Asc77.conjSub_normalizer g V]
  have h := Asc77.conjSub_le_iff (A := X) (B := Subgroup.normalizer (V : Set G)) g⁻¹
  rw [inv_inv] at h
  exact h.symm

private theorem perpD_mem_dSet_conj_iff (h : EndHyp Ω) (g : G) (X V : Subgroup G) :
    X ∈ DSet Ω (conjSub g V) ↔ conjSub g⁻¹ X ∈ DSet Ω V := by
  rw [h.mem_dSet_iff, h.mem_dSet_iff, perpD_le_normalizer_conj_iff]
  constructor
  · rintro ⟨hX, hN⟩
    exact ⟨h.thmD.hyp.conjInvariant g⁻¹ X hX, hN⟩
  · rintro ⟨hY, hN⟩
    have hX := h.thmD.hyp.conjInvariant g _ hY
    rw [conjSub_conjSub_inv] at hX
    exact ⟨hX, hN⟩

private theorem perpD_mem_kPerp_conj_iff (h : EndHyp Ω) (g : G) (X R : Subgroup G) :
    X ∈ KPerp Ω (conjSub g R) ↔ conjSub g⁻¹ X ∈ KPerp Ω R := by
  have hX : X = conjSub g R ↔ conjSub g⁻¹ X = R :=
    ⟨fun e => by rw [e, conjSub_inv_conjSub], fun e => by rw [← e, conjSub_conjSub_inv]⟩
  have hO : X ∈ omegaNbr Ω (conjSub g R) ↔ conjSub g⁻¹ X ∈ omegaNbr Ω R := by
    rw [TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two, TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two,
      perpD_le_normalizer_conj_iff]
    constructor
    · rintro ⟨hXΩ, hne, hN⟩
      exact ⟨h.thmD.hyp.conjInvariant g⁻¹ X hXΩ, (not_congr hX).mp hne, hN⟩
    · rintro ⟨hYΩ, hne, hN⟩
      have hXΩ := h.thmD.hyp.conjInvariant g _ hYΩ
      rw [conjSub_conjSub_inv] at hXΩ
      exact ⟨hXΩ, (not_congr hX).mpr hne, hN⟩
  rw [perpD_mem_KPerp_iff, perpD_mem_KPerp_iff, hX, hO]

private theorem perpD_ncard_conj (h : EndHyp Ω) (g : G) (R V : Subgroup G) :
    (KPerp Ω R ∩ DSet Ω V).ncard = (KPerp Ω (conjSub g R) ∩ DSet Ω (conjSub g V)).ncard := by
  refine Set.ncard_congr (fun X _ => conjSub g X) ?_ ?_ ?_
  · intro X hX
    refine ⟨(perpD_mem_kPerp_conj_iff h g (conjSub g X) R).mpr ?_,
      (perpD_mem_dSet_conj_iff h g (conjSub g X) V).mpr ?_⟩
    · rw [conjSub_inv_conjSub]
      exact hX.1
    · rw [conjSub_inv_conjSub]
      exact hX.2
  · intro X _ Y _ e
    exact conjSub_injective g e
  · intro Y hY
    exact ⟨conjSub g⁻¹ Y, ⟨(perpD_mem_kPerp_conj_iff h g Y R).mp hY.1,
      (perpD_mem_dSet_conj_iff h g Y V).mp hY.2⟩, conjSub_conjSub_inv g Y⟩

private theorem perpD_class_ncard_eq (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R R' : Subgroup G} (hR : R ∈ DSet Ω W) (hR' : R' ∈ DSet Ω W) :
    (KPerp Ω R ∩ DSet Ω W).ncard = (KPerp Ω R' ∩ DSet Ω W).ncard := by
  rcases h.mu W hW with h3 | h4 | hw
  · rw [(dSet_class_ncard h hW hR).1 h3, (dSet_class_ncard h hW hR').1 h3]
  · rw [(dSet_class_ncard h hW hR).2.1 h4, (dSet_class_ncard h hW hR').2.1 h4]
  · rw [(dSet_class_ncard h hW hR).2.2 hw, (dSet_class_ncard h hW hR').2.2 hw]

theorem clique_ncard_le (h : EndHyp Ω) {C : Set (Subgroup G)} (hC : C ⊆ Ω)
    (hcomm : ∀ R ∈ C, ∀ T ∈ C, R ≠ T → ∀ x ∈ R, ∀ y ∈ T, x * y = y * x)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    C.ncard ≤ (KPerp Ω R ∩ DSet Ω W).ncard := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨R', hR'C⟩
  · simp
  obtain ⟨W', hW', hCW'⟩ := perpD_exists_wSet h hC hcomm
  obtain ⟨g, rfl⟩ := wSet_conj h hW hW'
  have hsub : C ⊆ KPerp Ω R' ∩ DSet Ω (conjSub g W) := fun T hT =>
    ⟨perpD_clique_sub_kPerp h hC hcomm hR'C hT, hCW' hT⟩
  have h1 : C.ncard ≤ (KPerp Ω R' ∩ DSet Ω (conjSub g W)).ncard := Set.ncard_le_ncard hsub
  have h2 := perpD_ncard_conj h g (conjSub g⁻¹ R') W
  rw [conjSub_conjSub_inv] at h2
  have hR'' : conjSub g⁻¹ R' ∈ DSet Ω W := (perpD_mem_dSet_conj_iff h g R' W).mp (hCW' hR'C)
  exact h1.trans_eq (h2.symm.trans (perpD_class_ncard_eq h hW hR'' hR))

end CFSG.ClassicalInvolution.Q3.Sec13
