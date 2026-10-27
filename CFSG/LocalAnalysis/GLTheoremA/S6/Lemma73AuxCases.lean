module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l73_Cx_le_normalizer (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hB : IsSStarMax 3 B x L) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have h := sstarMax_layer_eq hc hB
  have h2 := L62.le_normalizer_glaPLayer 3 (Subgroup.centralizer ({x} : Set G))
  rwa [h] at h2

theorem l73_comm_eq_inf {B U : Subgroup G} {x : G} {L : Subgroup G} (hdir : IsDirectZpowersInf B x L)
    (hUx : U ≤ Subgroup.centralizer ({x} : Set G)) (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    (⁅U, B⁆ : Subgroup G) = ⁅U, B ⊓ L⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl inf_le_left)
  have hxB : Subgroup.zpowers x ≤ B := by rw [hdir.1]; exact le_sup_left
  have hsub : Subgroup.zpowers x ⊔ (B ⊓ L) ≤ B := sup_le hxB inf_le_left
  have key : ∀ b ∈ B, ∃ k ∈ B ⊓ L, ∀ u ∈ U, b * u * b⁻¹ = k * u * k⁻¹ := by
    intro b hb
    rw [hdir.1, Subgroup.sup_eq_closure] at hb
    induction hb using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        refine ⟨1, Subgroup.one_mem _, fun u hu => ?_⟩
        have hc : Commute u x := Subgroup.mem_centralizer_singleton_iff.1 (hUx hu)
        have := (hc.zpow_right i).eq
        rw [← this]
        simp
      · exact ⟨z, hz, fun u _ => rfl⟩
    | one => exact ⟨1, Subgroup.one_mem _, fun u _ => by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨ka, hka, hkaa⟩ := iha
      obtain ⟨kb, hkb, hkbb⟩ := ihb
      refine ⟨ka * kb, Subgroup.mul_mem _ hka hkb, fun u hu => ?_⟩
      have hbB : b ∈ B := by
        have : b ∈ Subgroup.zpowers x ⊔ (B ⊓ L) := by rw [Subgroup.sup_eq_closure]; exact hb
        exact hsub this
      have h1 : b * u * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hBU hbB) u).1 hu
      calc a * b * u * (a * b)⁻¹ = a * (b * u * b⁻¹) * a⁻¹ := by group
        _ = ka * (b * u * b⁻¹) * ka⁻¹ := hkaa _ h1
        _ = ka * (kb * u * kb⁻¹) * ka⁻¹ := by rw [hkbb u hu]
        _ = (ka * kb) * u * (ka * kb)⁻¹ := by group
    | inv a ha iha =>
      obtain ⟨ka, hka, hkaa⟩ := iha
      refine ⟨ka⁻¹, Subgroup.inv_mem _ hka, fun u hu => ?_⟩
      have haB : a ∈ B := by
        have : a ∈ Subgroup.zpowers x ⊔ (B ⊓ L) := by rw [Subgroup.sup_eq_closure]; exact ha
        exact hsub this
      have hu' : a⁻¹ * u * a ∈ U := by
        have := (Subgroup.mem_normalizer_iff.1 (hBU (B.inv_mem haB)) u).1 hu
        simpa using this
      have h2 := hkaa _ hu'
      have h3 : u = ka * (a⁻¹ * u * a) * ka⁻¹ := by
        calc u = a * (a⁻¹ * u * a) * a⁻¹ := by group
          _ = ka * (a⁻¹ * u * a) * ka⁻¹ := h2
      calc a⁻¹ * u * a⁻¹⁻¹ = a⁻¹ * u * a := by simp
        _ = ka⁻¹ * u * ka := by
          calc a⁻¹ * u * a = ka⁻¹ * (ka * (a⁻¹ * u * a) * ka⁻¹) * ka := by group
            _ = ka⁻¹ * u * ka := by rw [← h3]
        _ = ka⁻¹ * u * ka⁻¹⁻¹ := by simp
  refine Subgroup.commutator_le.2 fun u hu b hb => ?_
  obtain ⟨k, hk, hkb⟩ := key b hb
  have hu' : u⁻¹ ∈ U := U.inv_mem hu
  have : ⁅u, b⁆ = ⁅u, k⁆ := by
    have h1 := hkb u⁻¹ hu'
    simp only [commutatorElement_def]
    calc u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) := by group
      _ = u * (k * u⁻¹ * k⁻¹) := by rw [h1]
      _ = u * k * u⁻¹ * k⁻¹ := by group
  rw [this]
  exact Subgroup.commutator_mem_commutator hu hk

theorem l73_contra_three_dvd (hc : S6Ctx G 3) (i203 : I203At) {B : Subgroup G} {x : G} {L : Subgroup G}
    {n : ℕ} {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J)
    (hn : n = 9 ∨ n = 12) (hBL : Nat.card ↥(B ⊓ L : Subgroup G) = 3 ^ (n / 3)) : False := by
  obtain ⟨U, hUx, hU2, hBU, hUB, hU0⟩ := exists_two_group_comm_eq hc.prime hc.odd
    (GLAIsBmax.isPGroup (IsSStarMax.bmax hB)) (IsSStarMax.essential hB)
  have hUe : (⁅U, B ⊓ L⁆ : Subgroup G) = U := by
    rw [← l73_comm_eq_inf S.B_eq hUx hBU]; exact hUB
  have hCx := l73_Cx_le_normalizer hc hB
  have hUL : U ≤ L := by
    rw [← hUe]
    have h1 : (⁅U, B ⊓ L⁆ : Subgroup G) ≤ ⁅L, U⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono inf_le_right le_rfl
    exact h1.trans (commutator_le_left_of_normalizes (fun u hu => hCx (hUx hu)))
  obtain ⟨e⟩ := S.alt
  have hn5 : 5 ≤ n := by omega
  have hdvd : 3 ∣ n := by rcases hn with rfl | rfl <;> norm_num
  have hBLel : IsElemAbelian 3 (B ⊓ L : Subgroup G) :=
    isElemAbelian_mono (IsSStarMax.bmax hB).1 inf_le_left
  obtain ⟨hE1, hE2⟩ := imageMod_elemAbelian hc.prime (inf_le_right : B ⊓ L ≤ L) hBLel
  have hBLn : B ⊓ L ≤ Subgroup.normalizer (U : Set G) := inf_le_left.trans hBU
  obtain ⟨hU2', hN⟩ := l72_imageMod_facts (p := 3) (inf_le_right : B ⊓ L ≤ L) hUL hU2 hBLn
  have hbot : imageMod 3 L U = ⊥ :=
    i203 3 n hc.prime hc.odd hdvd hn5 (PQuot 3 L) e (imageMod 3 L (B ⊓ L)) (imageMod 3 L U) hE1
      (hE2.trans hBL) hU2' hN
  have hUO : U ≤ GLAPPrimeCoreOf 3 L := (imageMod_eq_bot_iff hUL).1 hbot
  have h415 := hc.stage4.1 B x L hB.1.1
  have hsn : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := (IsSStarMax.component hB).2.1
  have hOle : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hc.prime hsn
  have hle : U ≤ (⁅L, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))⁆ : Subgroup G) := by
    rw [← hUe]
    calc (⁅U, B ⊓ L⁆ : Subgroup G) ≤ ⁅GLAPPrimeCoreOf 3 L, L⁆ := Subgroup.commutator_mono hUO inf_le_right
      _ = ⁅L, GLAPPrimeCoreOf 3 L⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅L, GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))⁆ := Subgroup.commutator_mono le_rfl hOle
  exact false_of_twoGroup_le_odd hU2 hU0 hle h415

theorem l73_n9 (hc : S6Ctx G 3) (i203 : I203At) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 9 y J) : False :=
  l73_contra_three_dvd hc i203 hB S (Or.inl rfl) (by
    have := l73_card_BL hc hB S (by norm_num)
    simpa using this)


theorem inf_centralizer_D_eq {K D : Subgroup G} {a b : G} (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hD : D = Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    K ⊓ Subgroup.centralizer (D : Set G) = K ⊓ Subgroup.centralizer ({b} : Set G) := by
  have hC : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [hD, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union,
      Set.mem_singleton_iff, or_imp, forall_and, forall_eq]
  rw [hC, ← inf_assoc, inf_eq_left.2 hKa]

theorem isRootAlt_of_transport {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂] {k N m₀ : ℕ} (hk : 7 ≤ k)
    (e₁ : Q₁ ≃* ↥(alternatingGroup (Fin k))) (e₂ : Q₂ ≃* ↥(alternatingGroup (Fin N)))
    {H : Subgroup Q₂} (hH : IsRootAlt e₂ H k) (θ : Q₁ ≃* ↥H) {T : Subgroup Q₁}
    (hT : IsRootAlt e₂ (T.map (H.subtype.comp θ.toMonoidHom)) m₀) : IsRootAlt e₁ T m₀ := by
  classical
  set φ : Q₁ →* Q₂ := H.subtype.comp θ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := H.subtype_injective.comp θ.injective
  refine ⟨?_, ?_⟩
  · obtain ⟨u⟩ := hT.1
    exact ⟨(Subgroup.equivMapOfInjective T φ hφinj).trans u⟩
  · let P : ↥(alternatingGroup (Fin k)) →* ↥(alternatingGroup (Fin N)) :=
      (e₂.toMonoidHom.comp φ).comp e₁.symm.toMonoidHom
    have hPinj : Function.Injective P := (e₂.injective.comp hφinj).comp e₁.symm.injective
    have hPe : ∀ t : Q₁, P (e₁ t) = e₂ (φ t) := fun t => by
      show e₂ (φ (e₁.symm (e₁ t))) = _
      rw [e₁.symm_apply_apply]
    set Ω : Finset (Fin N) := (Set.toFinite (movedLettersOf e₂ H)).toFinset with hΩ
    have hΩcard : Ω.card = k := by
      rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
      exact hH.2
    have hΩmem : ∀ x, x ∈ Ω ↔ x ∈ movedLettersOf e₂ H := fun x => Set.Finite.mem_toFinset _
    have hsupp : ∀ g, ((P g : ↥(alternatingGroup (Fin N))) : Equiv.Perm (Fin N)).support ⊆ Ω := by
      intro g x hx
      rw [hΩmem]
      exact ⟨φ (e₁.symm g), (θ (e₁.symm g)).2, Equiv.Perm.mem_support.1 hx⟩
    obtain ⟨f, hfinj, hfrange, hf⟩ := exists_alt_embedding_support (Or.inr hk) P hPinj Ω hΩcard hsupp
    have himage : movedLettersOf e₂ (T.map φ) = f '' movedLettersOf e₁ T := by
      ext x
      constructor
      · rintro ⟨t', ⟨t, ht, rfl⟩, hx⟩
        have hxΩ : x ∈ Ω := by
          rw [← hPe t] at hx
          exact hsupp _ (Equiv.Perm.mem_support.2 hx)
        obtain ⟨i, rfl⟩ : x ∈ Set.range f := by rw [hfrange]; exact hxΩ
        refine ⟨i, ⟨t, ht, fun hti => hx ?_⟩, rfl⟩
        rw [← hPe t, hf, hti]
      · rintro ⟨i, ⟨t, ht, hti⟩, rfl⟩
        refine ⟨φ t, ⟨t, ht, rfl⟩, fun hx => hti (hfinj ?_)⟩
        rw [← hf, hPe t]
        exact hx
    have h2 := hT.2
    unfold MovesExactly at h2 ⊢
    rw [himage, Set.ncard_image_of_injective _ hfinj] at h2
    exact h2

theorem exists_equiv_imageMod_map {p : ℕ} {I J K : Subgroup G} (hI : I ≤ J) (hJ : J ≤ K)
    (hker : J ⊓ GLAPPrimeCoreOf p K = GLAPPrimeCoreOf p J) :
    ∃ θ : PQuot p J ≃* ↥(imageMod p K J),
      (imageMod p J I).map ((imageMod p K J).subtype.comp θ.toMonoidHom) = imageMod p K I := by
  obtain ⟨θ, hθ⟩ := l72_equiv_of_kernel hJ hker
  refine ⟨θ, ?_⟩
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hw
    exact ⟨⟨(i : G), hJ i.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hi),
      (hθ i).symm⟩
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hz
    have hiI : (i : G) ∈ I := Subgroup.mem_subgroupOf.1 hi
    exact ⟨QuotientGroup.mk (⟨(i : G), hI hiI⟩ : ↥J),
      Subgroup.mem_map.2 ⟨⟨(i : G), hI hiI⟩, Subgroup.mem_subgroupOf.2 hiI, rfl⟩, hθ _⟩

theorem l73_root_in_J {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J T I : Subgroup G}
    (S : AltSetup 3 B x L n y J) (hTI : L73TI B x L n y J T I)
    (hn : 6 < n - 3) (eJ : PQuot 3 J ≃* ↥(alternatingGroup (Fin (n - 3)))) :
    IsRootAlt eJ (imageMod 3 J I) (n - 4) := by
  classical
  obtain ⟨e, hcyc, ⟨Ω₄, hΩ₄, -, hI⟩, hJ⟩ := hTI.root
  have hp : Nat.Prime 3 := Nat.prime_three
  have hs3 : (permOfMod 3 L n e y).support.card = 3 := card_support_eq_of_cycleType hcyc.2
  have hJL : J ≤ L := S.J_comp.1.trans inf_le_left
  have hrootJ : IsRootAlt e (imageMod 3 L J) (n - 3) := by
    have := isRootAlt_altFixSub e (permOfMod 3 L n e y).support (by rw [hs3]; omega)
    rwa [hs3, ← hJ] at this
  have hrootI : IsRootAlt e (imageMod 3 L I) (n - 4) := by
    have := isRootAlt_altFixSub e Ω₄ (by rw [hΩ₄]; omega)
    rwa [hΩ₄, ← hI] at this
  obtain ⟨u⟩ := hrootJ.1
  have hcard5 : 5 ≤ Nat.card (Fin (n - 3)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  haveI : IsSimpleGroup (alternatingGroup (Fin (n - 3))) := alternatingGroup.isSimpleGroup hcard5
  have hsimple : IsSimpleGroup ↥(imageMod 3 L J) := u.isSimpleGroup
  have hdvd : 3 ∣ Nat.card ↥(imageMod 3 L J) := by
    rw [Nat.card_congr u.toEquiv]
    exact p_dvd_card_alternatingGroup hp (by norm_num) (le_trans (by norm_num) hcard5)
  have hker : J ⊓ GLAPPrimeCoreOf 3 L = GLAPPrimeCoreOf 3 J :=
    le_antisymm (inf_primeCoreOf_le hp hJL)
      (le_inf (Subgroup.map_subtype_le _) (primeCore_le_of_imageMod_simple hp hJL hsimple hdvd))
  obtain ⟨θ, hθ⟩ := exists_equiv_imageMod_map hTI.I_le_J hJL hker
  exact isRootAlt_of_transport (by omega) eJ e hrootJ θ (by rw [hθ]; exact hrootI)

theorem l73_central_shape {K J D : Subgroup G} {a b : G} (hS : L72Single 3 D J K a)
    (hDab : D = Subgroup.zpowers a ⊔ Subgroup.zpowers b) (hb : CentMod 3 K b) (hb3 : b ^ 3 = 1) {m : ℕ}
    (hm : 5 ≤ m) (hJ : IsAltPType 3 J m) :
    J ⊓ GLAPPrimeCoreOf 3 K = GLAPPrimeCoreOf 3 J ∧ IsAltPType 3 K m ∧
      ∃ e : PQuot 3 K ≃* ↥(alternatingGroup (Fin m)), IsRootAlt e (imageMod 3 K J) m := by
  classical
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := hS.comp.1
  have hJb : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J := by
    rw [← inf_centralizer_D_eq hKa hDab]
    exact hS.J_comp
  have hbp : IsPGroup 3 (Subgroup.zpowers b) := by
    rw [isPGroup_zpowers_iff_exists_pow]
    exact ⟨1, by simpa using hb3⟩
  obtain ⟨-, hall, -, -, hcov, -⟩ := glaPLayer_inf_centralizer Nat.prime_three hS.comp hbp hb
  have hJeq : J = GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) := hall J hJb
  have hJcov : J ⊔ GLAPPrimeCoreOf 3 K = K := by
    rw [hJeq]
    exact hcov
  have hJK : J ≤ K := hS.J_le
  obtain ⟨hker, ⟨eq⟩⟩ := cover_facts Nat.prime_three hJK hJcov
  obtain ⟨e₁⟩ := hJ
  have htop : imageMod 3 K J = ⊤ := imageMod_eq_top_of_sup hJK hJcov
  refine ⟨hker.symm, ⟨eq.symm.trans e₁⟩, eq.symm.trans e₁, ?_⟩
  rw [htop]
  exact isRootAlt_top (by omega) _

theorem l73_rootK (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (S : AltSetup 3 B x L n y J) {a : G} {K T I Sg : Subgroup G}
    (C : L73Ctx B x L n y J a K T I Sg) (hK : L72Single 3 (altDxy x y) J K a) {b : G}
    (hbD : b ∈ altDxy x y) (hDab : altDxy x y = Subgroup.zpowers a ⊔ Subgroup.zpowers b) {N : ℕ}
    (eK : PQuot 3 K ≃* ↥(alternatingGroup (Fin N))) (hn : 6 < n - 3) :
    ∃ (N' : ℕ) (e' : PQuot 3 K ≃* ↥(alternatingGroup (Fin N'))), n - 4 ≤ N' ∧
      IsRootAlt e' (imageMod 3 K I) (n - 4) := by
  obtain ⟨eJ⟩ := S.J_alt
  have hroot := l73_root_in_J S C.ti hn eJ
  have hb3 : b ^ 3 = 1 := S.isElemAbelian_D.2 b hbD
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := hK.comp.1
  have hJb : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J := by
    rw [← inf_centralizer_D_eq hKa hDab]; exact hK.J_comp
  have hSh : L72Shape 3 n J K := by
    by_cases hb : CentMod 3 K b
    · obtain ⟨hker, -, e, hr⟩ := l73_central_shape hK hDab hb hb3 (m := n - 3) (by omega) S.J_alt
      exact ⟨hker, _, e, hr⟩
    · obtain ⟨hr, hker⟩ := l72_root_of_alt (X := Subgroup.centralizer ({a} : Set G)) hc.prime hc.odd
        hK.comp (hK.norm hbD) hb3 hb hJb (by omega) S.J_alt eK
      exact ⟨hker, N, eK, hr⟩
  exact l72_transport C.ti.I_le_J hK.J_le hn (by omega) hSh eJ hroot

theorem l73_S_le_core_of_cen {K I S : Subgroup G} (hIK : I ≤ K) (hSK : S ≤ K) (hSI : S ≤ ⁅S, I⁆)
    (hcen : imageMod 3 K I ≤ Subgroup.centralizer ((imageMod 3 K S : Subgroup (PQuot 3 K)) :
      Set (PQuot 3 K))) : S ≤ GLAPPrimeCoreOf 3 K :=
  hSI.trans (l72_comm_le_core hIK hSK hcen)

theorem l73_S_le_core (i2013 : I2013At) {K I S : Subgroup G} (hIK : I ≤ K) (hSK : S ≤ K) (hS2 : IsPGroup 2 S)
    (hIS : I ≤ Subgroup.normalizer (S : Set G)) (hSI : S ≤ ⁅S, I⁆) {N' m : ℕ}
    (e' : PQuot 3 K ≃* ↥(alternatingGroup (Fin N'))) (h5 : 5 ≤ m) (hm : m ≤ N')
    (hroot : IsRootAlt e' (imageMod 3 K I) m) : S ≤ GLAPPrimeCoreOf 3 K := by
  obtain ⟨hT2, hnorm⟩ := l72_imageMod_facts (p := 3) hIK hSK hS2 hIS
  have hcen := i2013 (PQuot 3 K) N' m e' (imageMod 3 K I) h5 hm hroot (imageMod 3 K S) hT2 hnorm
  exact l73_S_le_core_of_cen hIK hSK hSI hcen

private theorem y5x_exists_E_cycle {L J : Subgroup G} {n : ℕ} {y : G} (hyL : y ∈ L)
    (e : PQuot 3 L ≃* ↥(alternatingGroup (Fin n)))
    (hcyc : (permOfMod 3 L n e y).cycleType = {3})
    (hJbar : (imageMod 3 L J).map e.toMonoidHom =
      fixingSubgroup (alternatingGroup (Fin n)) ((permOfMod 3 L n e y).support : Set (Fin n)))
    (hy3 : y ^ 3 = 1) {k : ℤ} (hyk : y ^ k ∈ J) : y ^ k = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ↥L →* Equiv.Perm (Fin n), ∀ u : ↥L,
      Φ u = ((e (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) u) : ↥(alternatingGroup (Fin n))) :
        Equiv.Perm (Fin n)) :=
    ⟨(alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))), fun u => rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : Equiv.Perm (Fin n), σ = permOfMod 3 L n e y := ⟨_, rfl⟩
  rw [← hσdef] at hcyc hJbar
  have hσ : σ = Φ ⟨y, hyL⟩ := by
    rw [hσdef, hΦ]
    unfold permOfMod
    rw [dif_pos hyL]
    rfl
  have hy3z : y ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hy3]
  obtain ⟨u, hu⟩ : ∃ u : ↥L, u = (⟨y, hyL⟩ : ↥L) ^ k := ⟨_, rfl⟩
  have hu_val : (u : G) = y ^ k := by
    rw [hu, Subgroup.coe_zpow]
  have hu_J : (u : G) ∈ J := by
    rw [hu_val]
    exact hyk
  have hfix : ∀ z ∈ σ.support, (Φ u) z = z := by
    intro z hz
    have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) u ∈ imageMod 3 L J :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hu_J)
    have hmem2 := Subgroup.mem_map_of_mem e.toMonoidHom hmem
    rw [hJbar, mem_fixingSubgroup_iff] at hmem2
    have hz' := hmem2 z (Finset.mem_coe.2 hz)
    rw [hΦ]
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hz'
  have hσpow : σ ^ k = Φ u := by
    rw [hσ, hu, map_zpow]
  have hσk : σ ^ k = 1 := by
    apply Equiv.ext
    intro z
    rw [Equiv.Perm.one_apply]
    by_cases hz : σ z = z
    · exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hz k
    · rw [hσpow]
      exact hfix z (Equiv.Perm.mem_support.2 hz)
  have hw3 : (⟨y, hyL⟩ : ↥L) ^ (3 : ℤ) = 1 :=
    Subtype.ext (by rw [Subgroup.coe_zpow]; exact hy3z)
  have hσ3 : σ ^ (3 : ℤ) = 1 := by
    rw [hσ, ← map_zpow, hw3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, Equiv.Perm.cycleType_one] at hcyc
    simp at hcyc
  have hσ3n : σ ^ 3 = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at hσ3
    exact hσ3
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3n hσ1
  have hdvd : ((orderOf σ : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hσk
  rw [hord] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hy3n : y ^ ((3 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]
    exact hy3
  rw [hc, zpow_mul, hy3n, one_zpow]

theorem l73_exists_E {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G} {J : Subgroup G}
    (hc : S6Ctx G 3) (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) :
    ∃ E : Subgroup G, altDxy x y ≤ E ∧ IsElemAbelian 3 E ∧
      E ≤ Subgroup.centralizer (altDxy x y : Set G) ∧ Nat.card ↥E = 3 ^ (n / 3 + 1) := by
  classical
  have hn9 : 9 ≤ n := by
    have := S.three_mul_le
    omega
  have hxD : x ∈ altDxy x y := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyD : y ∈ altDxy x y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hJL : J ≤ L := S.J_comp.1.trans inf_le_left
  have hJD : J ≤ Subgroup.centralizer (altDxy x y : Set G) := S.J_comp.1.trans inf_le_right
  obtain ⟨EJ, hEJJ, hEJel, hEJcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) J
  rw [S.rank_J] at hEJcard
  have hEJD : EJ ≤ Subgroup.centralizer (altDxy x y : Set G) := hEJJ.trans hJD
  have hy3 : y ^ 3 = 1 := S.y_order ▸ pow_orderOf_eq_one y
  have hDJ : altDxy x y ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    rintro h ⟨hhD, hhJ⟩
    rw [Subgroup.mem_bot]
    have hzD : Subgroup.zpowers y ≤ altDxy x y := Subgroup.zpowers_le.2 hyD
    have hxC : x ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun g hg =>
        isElemAbelian_commute S.isElemAbelian_D (hzD hg) hxD
    have hA : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
      Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hxC)
    obtain ⟨a', ha', n', hn', hh⟩ := exists_mul_of_mem_sup_of_le_normalizer hA hhD
    have hnL : n' ∈ L := (Subgroup.zpowers_le.2 S.y_mem) hn'
    have haL : a' ∈ L := by
      have hdiv : a' = h * n'⁻¹ := by rw [hh, mul_inv_cancel_right]
      rw [hdiv]
      exact L.mul_mem (hJL hhJ) (L.inv_mem hnL)
    have haB : a' ∈ B := (Subgroup.zpowers_le.2 (IsSStarMax.essential hB).1) ha'
    have ha1 : a' = 1 := by
      have hmem : a' ∈ Subgroup.zpowers x ⊓ (B ⊓ L) :=
        Subgroup.mem_inf.2 ⟨ha', Subgroup.mem_inf.2 ⟨haB, haL⟩⟩
      rw [S.B_eq.2] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hhn : h = n' := by rw [hh, ha1, one_mul]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn'
    have hyk : y ^ k ∈ J := by
      rw [hk, ← hhn]
      exact hhJ
    obtain ⟨e, hpc, hJbar⟩ := S.cycle
    calc h = n' := hhn
      _ = y ^ k := hk.symm
      _ = 1 := y5x_exists_E_cycle S.y_mem e hpc.2 hJbar hy3 hyk
  have hinf : altDxy x y ⊓ EJ = ⊥ := le_bot_iff.1 ((inf_le_inf_left _ hEJJ).trans hDJ.le)
  have hDE : altDxy x y ≤ Subgroup.centralizer (EJ : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun e he =>
      ((Subgroup.mem_centralizer_iff.1 (hEJD he)) d hd).symm
  have hcomm : ∀ d ∈ altDxy x y, ∀ e ∈ EJ, d * e = e * d := fun d hd e he =>
    Subgroup.mem_centralizer_iff.1 (hEJD he) d hd
  have hEel : IsElemAbelian 3 (altDxy x y ⊔ EJ) :=
    isElemAbelian_sup_of_commute S.isElemAbelian_D hEJel hcomm
  have hDD : altDxy x y ≤ Subgroup.centralizer (altDxy x y : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun h hh => isElemAbelian_commute S.isElemAbelian_D hh hd
  have hEC : altDxy x y ⊔ EJ ≤ Subgroup.centralizer (altDxy x y : Set G) := sup_le hDD hEJD
  have hcardD := card_sup_mul_card_inf_of_le_normalizer (A := altDxy x y) (B := EJ)
    (hEJD.trans (Subgroup.centralizer_le_normalizer _))
  rw [hinf, Subgroup.card_bot, mul_one, S.card_D, hEJcard] at hcardD
  refine ⟨altDxy x y ⊔ EJ, le_sup_left, hEel, hEC, ?_⟩
  rw [hcardD, ← pow_add]
  congr 1
  omega

theorem l73_five_of_core (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 12 y J) {a : G} {K T I Sg : Subgroup G}
    (C : L73Ctx B x L 12 y J a K T I Sg) (hSO : Sg ≤ GLAPPrimeCoreOf 3 K) :
    ∃ E U : Subgroup G, IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card ↥E ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨E, hDE, hEel, hECD, hEcard⟩ := l73_exists_E hc hB S
  have hEa : E ≤ Subgroup.centralizer ({a} : Set G) :=
    hECD.trans (Subgroup.centralizer_le (by simpa using C.a_mem))
  have hsn : IsSubnormal K (Subgroup.centralizer ({a} : Set G)) := C.K_sn
  have hOle : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hc.prime hsn
  have hEO : E ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    hEa.trans (le_normalizer_glaPPrimeCoreOf 3 _)
  have hev : ¬ Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))) := fun hodd =>
    false_of_twoGroup_le_odd C.S_two C.S_ne (hSO.trans hOle) hodd
  obtain ⟨U, -, hU0, hU2, hEU⟩ := exists_invariant_twoGroup hc.prime hc.odd
    (isPGroup_of_isElemAbelian hEel) hEO
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hc.prime _) hev
  refine ⟨E, U, hEel, ?_, hU0, hU2, hEU⟩
  rw [hEcard]

theorem l73_five_of_coOne (i1016 : I1016CoAt G) {X K : Subgroup G} {a : G}
    (hK : GLAPComponent 3 X K) (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hCo : IsSporType 3 K .Co1) :
    ∃ E U : Subgroup G, IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card ↥E ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hZ, E₀, U, hE₀K, hE₀el, hE₀card, hUK, hU2, hUO, hE₀N⟩ := i1016 X K hK hCo
  have haN : ∀ S : Subgroup G, S ≤ K → a ∈ Subgroup.normalizer (S : Set G) := fun S hS =>
    Subgroup.centralizer_le_normalizer (S : Set G)
      (Subgroup.mem_centralizer_iff.2 fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (hKa (hS hs)))
  have haK : a ∉ K := by
    intro haK
    have hcenter : (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hKa g.2)
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcenter
    have haO : a ∈ GLAPPrimeCoreOf 3 K := Subgroup.mem_map.2 ⟨⟨a, haK⟩, hcenter, rfl⟩
    have hdvd : orderOf a ∣ Nat.card ↥(GLAPPrimeCoreOf 3 K) := Subgroup.orderOf_dvd_natCard _ haO
    rw [orderOf_eq_prime ha3 ha1] at hdvd
    have hcop := CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp K
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hacard : Nat.card ↥(Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, haord]
  have haEl : IsElemAbelian 3 (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha3
  have hcomm : ∀ e ∈ E₀, ∀ b ∈ Subgroup.zpowers a, e * b = b * e := fun e he b hb => by
    have haCe : a ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 (hKa (hE₀K he))).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.zpowers_le.2 haCe hb)).symm
  have hEel : IsElemAbelian 3 (E₀ ⊔ Subgroup.zpowers a) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE₀el haEl hcomm
  have hBN : Subgroup.zpowers a ≤ Subgroup.normalizer (E₀ : Set G) :=
    Subgroup.zpowers_le.2 (haN E₀ hE₀K)
  have hinf : E₀ ⊓ Subgroup.zpowers a = ⊥ := by
    have hdvd : Nat.card ↥(E₀ ⊓ Subgroup.zpowers a) ∣ Nat.card ↥(Subgroup.zpowers a) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hacard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : E₀ ⊓ Subgroup.zpowers a = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hacard])
      have haI : a ∈ E₀ ⊓ Subgroup.zpowers a := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact haK (hE₀K (Subgroup.mem_inf.1 haI).1)
  have hcardE : Nat.card ↥(E₀ ⊔ Subgroup.zpowers a) = 3 ^ 5 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hBN
    rw [hinf, Subgroup.card_bot, hE₀card, hacard, mul_one] at h
    rw [h]
    norm_num
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    exact hUO bot_le
  have hEN : E₀ ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (U : Set G) :=
    sup_le hE₀N (Subgroup.zpowers_le.2 (haN U hUK))
  exact ⟨E₀ ⊔ Subgroup.zpowers a, U, hEel, hcardE.ge, hU0, hU2, hEN⟩

theorem l73_n12 (hc : S6Ctx G 3) (i183 : Input18_3_4) (i112 : I112StarAt G 3) (hne : AltNotWeakExcAt)
    (i2013 : I2013At) (i203 : I203At) (i1415 : I1415NineAt G) (i2014 : I2014At G) (i1016 : I1016CoAt G)
    {B : Subgroup G} {x : G} {L : Subgroup G} {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L)
    (S : AltSetup 3 B x L 12 y J) {a : G} {K T I Sg : Subgroup G}
    (C : L73Ctx B x L 12 y J a K T I Sg) : False := by
  have hn : (7 : ℕ) < 12 - 3 := by norm_num
  have hK : L72Single 3 (altDxy x y) J K a := by
    rw [C.K_eq]; exact l72_single hc i183 i112 hne hB S hn C.a_mem C.a_ne
  obtain ⟨b, hbD, hba, hDab⟩ := exists_pair_of_card_sq hc.prime S.card_D C.a_mem C.a_ne
    S.isElemAbelian_D
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) := kGroup_centralizer hc C.a_ne
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := hK.comp.1
  have hJb : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J := by
    rw [← inf_centralizer_D_eq hKa hDab]; exact hK.J_comp
  have hb3 : b ^ 3 = 1 := S.isElemAbelian_D.2 b hbD
  have hbK : b ∈ Subgroup.normalizer (K : Set G) := hK.norm hbD
  have hJ9 : IsAltPType 3 J 9 := S.J_alt
  have hIK : I ≤ K := C.ti.I_le_J.trans hK.J_le
  have hSK : Sg ≤ K := C.S_le_K
  have h5 : ∃ E U : Subgroup G, IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card ↥E ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set G) := by
    have hA : ∀ {N : ℕ}, (PQuot 3 K ≃* ↥(alternatingGroup (Fin N))) →
        ∃ E U : Subgroup G, IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card ↥E ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
          E ≤ Subgroup.normalizer (U : Set G) := fun {N} eK => by
      obtain ⟨N', e', hN', hroot⟩ := l73_rootK hc S C hK hbD hDab eK (by norm_num)
      exact l73_five_of_core hc hB S C (l73_S_le_core i2013 hIK hSK C.S_two C.I_norm C.S_comm e'
        (by norm_num) hN' hroot)
    by_cases hb : CentMod 3 K b
    ·
      obtain ⟨-, ⟨eK⟩, -⟩ := l73_central_shape hK hDab hb hb3 (m := 9) (by norm_num) hJ9
      exact hA eK
    · rcases i1415 (Subgroup.centralizer ({a} : Set G)) K J b hXK hK.comp hbK hb3 hJb hJ9 with
        ⟨k, ⟨eK⟩⟩ | hHN | hCo
      · exact hA eK
      · have hI8 : IsAltPType 3 I 8 := C.ti.I_alt
        have hcen := i2014 (Subgroup.centralizer ({a} : Set G)) K J I Sg b hXK hK.comp hHN hbK hb3 hb
          hJb hJ9 C.ti.I_le_J hI8 hSK C.S_two C.I_norm (C.D_norm hbD)
        exact l73_five_of_core hc hB S C (l73_S_le_core_of_cen hIK hSK C.S_comm hcen)
      · exact l73_five_of_coOne i1016 hK.comp hKa C.a_ne (S.isElemAbelian_D.2 a C.a_mem) hCo
  obtain ⟨E, U, hE, hE5, hU0, hU2, hEU⟩ := h5
  have h1 := card_le_pow_glaTwoLocalRank hc.prime hE hU0 hU2 hEU
  have hBc := (IsSStarMax.bmax hB).2.1
  rw [← hBc] at h1
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hc.prime (IsSStarMax.bmax hB).1
  have hrk : CFSG.Open.pRank 3 B = k :=
    pRank_eq_of_isElemAbelian_altSetup hc.prime.one_lt (IsSStarMax.bmax hB).1 hk
  have h2 := S.rank_B
  rw [hrk] at h2
  have hk5 : 5 ≤ k := by
    rw [hk] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 (hE5.trans h1)
  have hk5' : k ≤ 5 := by omega
  have hmul := l73_card_B_mul hB S.B_eq
  rw [hk, show k = 5 by omega] at hmul
  exact l73_contra_three_dvd hc i203 hB S (Or.inr rfl) (by omega)

end CFSG.LocalAnalysis.GLTheoremA
