module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParC

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus)

section ParD

variable {G : Type} [Group G] [Finite G] {n : ℕ} {M L V : Subgroup G} (d : O6NatData G n L V)

theorem O6NatData.exists_frame (hn : 1 ≤ n) (hMV : M ≤ normalizer (V : Set G)) {T : Subgroup G}
    (hT : IsPGroup 2 T) :
    ∃ w u : OW d.F, LinearIndependent d.F ![w, u] ∧ quadMinus 3 d.F d.b d.c w = 0 ∧
      quadMinus 3 d.F d.b d.c u = 0 ∧ polar (quadMinus 3 d.F d.b d.c) w u = 0 ∧
      ∀ (t : G) (ht : t ∈ d.Lam hMV), t ∈ T →
        ∃ τ : d.F, gv (d.matHom hMV ⟨t, ht⟩) w = w ∧ gv (d.matHom hMV ⟨t, ht⟩) u = u + τ • w := by
  have hT1 : IsPGroup 2 ↥(T ⊓ d.Lam hMV) := hT.to_inf_left
  have hT2 : IsPGroup 2 ↥((T ⊓ d.Lam hMV).subgroupOf (d.Lam hMV)) := hT1.comap_subtype
  have hEp : IsPGroup 2 ↥(((T ⊓ d.Lam hMV).subgroupOf (d.Lam hMV)).map (d.matHom hMV)) :=
    hT2.map (d.matHom hMV)
  have hEO : ∀ g ∈ ((T ⊓ d.Lam hMV).subgroupOf (d.Lam hMV)).map (d.matHom hMV), ∀ v : OW d.F,
      quadMinus 3 d.F d.b d.c (gv g v) = quadMinus 3 d.F d.b d.c v := by
    rintro _ ⟨m, -, rfl⟩ v
    exact quadMinus_mulVec_of_mem_statedOmega (d.matHom_mem hMV m) v
  obtain ⟨w, u, -, hli, hQw, hQu, hpol, hE⟩ := exists_fixed_plane d.irred d.card_F hn hEO hEp
  refine ⟨w, u, hli, hQw, hQu, hpol, fun t ht htT => ?_⟩
  have hmem : d.matHom hMV ⟨t, ht⟩ ∈
      ((T ⊓ d.Lam hMV).subgroupOf (d.Lam hMV)).map (d.matHom hMV) :=
    Subgroup.mem_map.mpr ⟨⟨t, ht⟩, Subgroup.mem_subgroupOf.mpr ⟨htT, ht⟩, rfl⟩
  obtain ⟨τ, h1, h2⟩ := hE _ hmem
  exact ⟨τ, h1, h2⟩

noncomputable def O6NatData.radL (G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) : Subgroup ↥L :=
  (RadGrp d.b d.c).comap
    ((cvHom G₀).comp ((StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype.comp d.ε))

noncomputable def O6NatData.radG (G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) : Subgroup G :=
  (d.radL G₀).map L.subtype

theorem O6NatData.mem_radG (G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) {x : G} :
    x ∈ d.radG G₀ ↔ ∃ hx : x ∈ L, RadHyp d.b d.c (G₀⁻¹ *
      ((d.ε ⟨x, hx⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) * G₀) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem O6NatData.radG_isPGroup (G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
    IsPGroup 2 ↥(d.radG G₀) := by
  have hker : ((cvHom G₀).comp
      ((StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype.comp d.ε)).ker =
      CFSG.pCore 2 ↥L := by
    rw [MonoidHom.ker_comp_of_injective _ _ (cvHom_injective G₀),
      MonoidHom.ker_comp_of_injective _ _
        (StatedOmega (StatedQuadMinus 3 d.F d.b d.c)).subtype_injective, d.ε_ker]
  have h1 : IsPGroup 2 ↥(d.radL G₀) :=
    (RadGrp_isPGroup (b := d.b) (c := d.c)).comap_of_ker_isPGroup _
      (by rw [hker]; exact CFSG.pCore_isPGroup)
  exact h1.map L.subtype

theorem O6NatData.radG_conj_mem (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) {G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F}
    (hG₀iso : ∀ v : OW d.F, quadMinus 3 d.F d.b d.c (gv G₀ v) = quadMinus 3 d.F d.b d.c v)
    {w u : OW d.F} (hGw : gv G₀ (eV d.F idx0) = w) (hGu : gv G₀ (eV d.F idx1) = u)
    {t : G} (ht : t ∈ d.Lam hMV)
    (hfr : ∃ τ : d.F, gv (d.matHom hMV ⟨t, ht⟩) w = w ∧ gv (d.matHom hMV ⟨t, ht⟩) u = u + τ • w)
    (hfr' : ∃ τ : d.F, gv (d.matHom hMV ⟨t, ht⟩)⁻¹ w = w ∧
      gv (d.matHom hMV ⟨t, ht⟩)⁻¹ u = u + τ • w)
    {x : G} (hx : x ∈ d.radG G₀) : t * x * t⁻¹ ∈ d.radG G₀ := by
  obtain ⟨hxL, hrad⟩ := (d.mem_radG G₀).mp hx
  have htM : t ∈ M := d.Lam_le hMV ht
  have htxL : t * x * t⁻¹ ∈ L := (mem_normalizer_iff.mp (hML htM) x).mp hxL
  refine (d.mem_radG G₀).mpr ⟨htxL, ?_⟩
  have hmΩ := d.matHom_mem hMV ⟨t, ht⟩
  have hmiso : ∀ v : OW d.F, quadMinus 3 d.F d.b d.c (gv (d.matHom hMV ⟨t, ht⟩) v) =
      quadMinus 3 d.F d.b d.c v := fun v => quadMinus_mulVec_of_mem_statedOmega hmΩ v
  obtain ⟨τ, h1, h2⟩ := hfr
  obtain ⟨τ', h1', h2'⟩ := hfr'
  rw [d.eps_conj hLM hML hMV ht hxL htxL]
  exact rad_conj_conj hG₀iso hGw hGu hmiso (coeffs_of_frame h1 h2).1 (coeffs_of_frame h1 h2).2
    (coeffs_of_frame h1' h2').1 (coeffs_of_frame h1' h2').2 hrad

theorem O6NatData.parabolic_of_inputs {p : ℕ} (hn : 1 ≤ n) (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hMV : M ≤ normalizer (V : Set G))
    (hW : ∀ {w u : OW d.F}, LinearIndependent d.F ![w, u] → quadMinus 3 d.F d.b d.c w = 0 →
      quadMinus 3 d.F d.b d.c u = 0 → polar (quadMinus 3 d.F d.b d.c) w u = 0 →
      ∃ G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F,
        toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F G₀ ∈
          orthogonalGroup (quadMinus 3 d.F d.b d.c) ∧
        gv G₀ (eV d.F idx0) = w ∧ gv G₀ (eV d.F idx1) = u)
    (hP : ∀ Y : Submodule d.F (OW d.F), Module.finrank d.F Y = 2 →
      (∀ y ∈ Y, StatedQuadMinus 3 d.F d.b d.c y = 0) →
      ∃ P : Subgroup G, P ≤ L ∧ 2 ≤ CFSG.Open.pRank p P ∧ ∀ x ∈ P, ∃ hx : x ∈ L, ∀ y ∈ Y,
        gv ((d.ε ⟨x, hx⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) y ∈ Y) :
    ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ∃ P R : Subgroup G, P ≤ L ∧ R ≤ T ∧ 2 ≤ CFSG.Open.pRank p P ∧
        ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
          (∀ B : Subgroup G, B ≤ A → B.relIndex A < 2 ^ (2 * n) →
            V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G)) →
          A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) → ∀ a ∈ A, ∀ x ∈ P, ⁅x, a⁆ ∈ R := by
  intro T hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, u, hli, hQw, hQu, hpol, hframe⟩ := d.exists_frame hn hMV hT.isPGroup
  obtain ⟨G₀, hG₀O, hGw, hGu⟩ := hW hli hQw hQu hpol
  have hG₀iso : ∀ v : OW d.F, quadMinus 3 d.F d.b d.c (gv G₀ v) = quadMinus 3 d.F d.b d.c v :=
    gv_iso_of_mem hG₀O
  have hY2 := finrank_span_pair hli
  have hYs : ∀ y ∈ Submodule.span d.F ({w, u} : Set (OW d.F)),
      StatedQuadMinus 3 d.F d.b d.c y = 0 := by
    intro y hy
    obtain ⟨s, t, rfl⟩ := coeffs_of_mem_span hy
    rw [← quadMinus_eq_stated]
    exact quad_span_zero hQw hQu hpol s t
  obtain ⟨P, hPL, hPrk, hPstab⟩ := hP _ hY2 hYs
  refine ⟨P, d.radG G₀, hPL, ?_, hPrk, ?_⟩
  ·
    have hT0 : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ d.Lam hMV) (d.Lam hMV) :=
      hT.inf_of_le_normalizer (d.Lam_le hMV) (d.Lam_normal hLM hML hMV)
    have hRΛ : d.radG G₀ ≤ d.Lam hMV := fun x hx =>
      d.L_le_Lam hLM hMV ((d.mem_radG G₀).mp hx).1
    have hN : ∀ t ∈ T ⊓ d.Lam hMV, ∀ x ∈ d.radG G₀, t * x * t⁻¹ ∈ d.radG G₀ := by
      intro t ht x hx
      have htiΛ : t⁻¹ ∈ d.Lam hMV := (d.Lam hMV).inv_mem ht.2
      obtain ⟨τ, h1, h2⟩ := hframe t ht.2 ht.1
      obtain ⟨τ', h1', h2'⟩ := hframe t⁻¹ htiΛ (T.inv_mem ht.1)
      have hinv : d.matHom hMV ⟨t⁻¹, htiΛ⟩ = (d.matHom hMV ⟨t, ht.2⟩)⁻¹ :=
        map_inv (d.matHom hMV) ⟨t, ht.2⟩
      rw [hinv] at h1' h2'
      exact d.radG_conj_mem hLM hML hMV hG₀iso hGw hGu ht.2 ⟨τ, h1, h2⟩ ⟨τ', h1', h2'⟩ hx
    exact (pgroup_le_sylow_of_normalized hT0 hRΛ (d.radG_isPGroup G₀) hN).trans inf_le_left
  ·
    intro A hAT hA hQ hAL a ha x hxP
    have haT : a ∈ T := hAT ha
    have hAM : A ≤ M := hAT.trans hT.le
    have hAV : A ≤ normalizer (V : Set G) := hAM.trans hMV
    have hAΛ : A ≤ d.Lam hMV :=
      le_trans hAL (sup_le (d.L_le_Lam hLM hMV) (d.C_le_Lam hMV))
    have haΛ : a ∈ d.Lam hMV := hAΛ ha
    have hfixu : ∀ a' : ↥A, d.rho A hAV a' u = u := fun a' =>
      d.q_fixes hn hAV hQ (w := w) (fun a'' => by
        obtain ⟨τ, -, h2⟩ := hframe a''.1 (hAΛ a''.2) (hAT a''.2)
        exact ⟨τ, (d.act_eq_matHom hMV (hAΛ a''.2) (hAM a''.2) u).trans h2⟩) a'
    obtain ⟨τ₀, h1, -⟩ := hframe a haΛ haT
    have hmau : gv (d.matHom hMV ⟨a, haΛ⟩) u = u :=
      (d.act_eq_matHom hMV haΛ (hAM ha) u).symm.trans (hfixu ⟨a, ha⟩)
    have hmaΩ := d.matHom_mem hMV ⟨a, haΛ⟩
    have hρΩ : G₀⁻¹ * d.matHom hMV ⟨a, haΛ⟩ * G₀ ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c) :=
      conj_mem_omega_inv d.irred hG₀O hmaΩ
    have haa : a * a = 1 := by
      have := hA.2 a ha
      rwa [pow_two] at this
    have hma2 : d.matHom hMV ⟨a, haΛ⟩ * d.matHom hMV ⟨a, haΛ⟩ = 1 := by
      have h := map_mul (d.matHom hMV) ⟨a, haΛ⟩ ⟨a, haΛ⟩
      have e : (⟨a, haΛ⟩ : ↥(d.Lam hMV)) * ⟨a, haΛ⟩ = 1 := Subtype.ext haa
      rw [e, map_one] at h
      exact h.symm
    have hρ2 : (G₀⁻¹ * d.matHom hMV ⟨a, haΛ⟩ * G₀) * (G₀⁻¹ * d.matHom hMV ⟨a, haΛ⟩ * G₀) = 1 := by
      calc (G₀⁻¹ * d.matHom hMV ⟨a, haΛ⟩ * G₀) * (G₀⁻¹ * d.matHom hMV ⟨a, haΛ⟩ * G₀)
          = G₀⁻¹ * (d.matHom hMV ⟨a, haΛ⟩ * d.matHom hMV ⟨a, haΛ⟩) * G₀ := by group
        _ = 1 := by rw [hma2]; group
    have hρfix : ∀ i : Fin (3 - 1), gv (G₀⁻¹ * d.matHom hMV ⟨a, haΛ⟩ * G₀) (eV d.F i) =
        eV d.F i := by
      intro i
      have hi : i = idx0 ∨ i = idx1 := by
        revert i
        decide
      rcases hi with rfl | rfl
      · rw [gv_mul, gv_mul, hGw, h1, ← hGw, gv_inv_gv]
      · rw [gv_mul, gv_mul, hGu, hmau, ← hGu, gv_inv_gv]
    have hρrad : RadHyp d.b d.c (G₀⁻¹ * d.matHom hMV ⟨a, haΛ⟩ * G₀) :=
      rad_of_involution d.irred hρΩ hρ2 hρfix
    have hxL : x ∈ L := hPL hxP
    have hxaL : ⁅x, a⁆ ∈ L := by
      have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact L.mul_mem hxL ((mem_normalizer_iff.mp (hML (hAM ha)) x⁻¹).mp (L.inv_mem hxL))
    refine (d.mem_radG G₀).mpr ⟨hxaL, ?_⟩
    rw [d.eps_comm hLM hML hMV haΛ hxL hxaL]
    obtain ⟨hxL', hxst⟩ := hPstab x hxP
    obtain ⟨hxiL, hxist⟩ := hPstab x⁻¹ (P.inv_mem hxP)
    have hexinv : ((d.ε ⟨x⁻¹, hxiL⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) =
        ((d.ε ⟨x, hxL⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F)⁻¹ := by
      have e : (⟨x⁻¹, hxiL⟩ : ↥L) = (⟨x, hxL⟩ : ↥L)⁻¹ := rfl
      rw [e, map_inv, Subgroup.coe_inv]
    have hco := coeffs_of_stab hxst
    have hco' := coeffs_of_stab hxist
    rw [hexinv] at hco'
    have hexiso : ∀ v : OW d.F, quadMinus 3 d.F d.b d.c (gv ((d.ε ⟨x, hxL⟩ :
        ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) v) = quadMinus 3 d.F d.b d.c v :=
      fun v => quadMinus_mulVec_of_mem_statedOmega (d.ε ⟨x, hxL⟩).2 v
    exact rad_comm_conj hG₀iso hGw hGu hexiso hco.1 hco.2 hco'.1 hco'.2 hρrad

end ParD

end CFSG.LocalAnalysis.RankThreeUC
