module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveU
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapAE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP2

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

theorem fix_support_rho_of_perfect {M : Subgroup X} {n : ℕ}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} {b : X} (hbN : b ∈ normalizer (M : Set X))
    (hb2 : b * b = 1) (h4 : (ρ ⟨b, hbN⟩).support.card ≤ 4) {L : Subgroup X}
    (hLN : L ≤ normalizer (M : Set X)) (hLb : L ≤ centralizer ({b} : Set X))
    (hperf : ⁅L, L⁆ = L) {y : X} (hy : y ∈ L) :
    ∀ ω ∈ (ρ ⟨b, hbN⟩).support, ρ ⟨y, hLN hy⟩ ω = ω := by
  classical
  set φ : ↥L →* Perm (Fin n) := ρ.comp (inclusion hLN) with hφdef
  have htop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hperf]
  have hPperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hτ2 : ρ ⟨b, hbN⟩ * ρ ⟨b, hbN⟩ = 1 := by
    rw [← map_mul, show (⟨b, hbN⟩ : ↥(normalizer (M : Set X))) * ⟨b, hbN⟩ = 1 from
      Subtype.ext hb2, map_one]
  have hc : ∀ l ∈ φ.range, l * ρ ⟨b, hbN⟩ = ρ ⟨b, hbN⟩ * l := by
    rintro _ ⟨z, rfl⟩
    rw [hφdef, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLb z.2))
  exact CatFactsSmall.fix_support_of_perfect hτ2 h4 hPperf hc _ ⟨⟨y, hy⟩, rfl⟩

theorem fixedLayer_facts_of_perm [Finite X] {C M : Subgroup X} {n : ℕ} (hMC : M ≤ C)
    (hMpc : IsPComponent 2 (M.subgroupOf C))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {b : X}
    (hbN : b ∈ normalizer (M : Set X)) (hb2 : b * b = 1)
    (h4 : (ρ ⟨b, hbN⟩).support.card ≤ 4) (h5 : 5 ≤ n - (ρ ⟨b, hbN⟩).support.card) :
    GSLit.fixedLayer M (zpowers b) ≤ C ⊓ centralizer ({b} : Set X) ∧
      IsPComponent 2 ((GSLit.fixedLayer M (zpowers b)).subgroupOf
        (C ⊓ centralizer ({b} : Set X))) ∧
      Nonempty (↥(GSLit.fixedLayer M (zpowers b)) ⧸
          pPrimeCore 2 ↥(GSLit.fixedLayer M (zpowers b)) ≃*
        alternatingGroup ↥((ρ ⟨b, hbN⟩).supportᶜ : Finset (Fin n))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Jb, hJb, hJbpc, hmem, -, χ, -⟩ :=
    exists_fixed_component_of_perm hMC hMpc hρ hbN hb2 h5
  set Y : Subgroup X := M ⊓ centralizer ({b} : Set X) with hYdef
  have hfl : GSLit.fixedLayer M (zpowers b) = (pLayer ↥Y 2).map Y.subtype := by
    unfold GSLit.fixedLayer
    rw [centralizer_zpowers_eq' b]
  have hYC : Y ≤ C ⊓ centralizer ({b} : Set X) := inf_le_inf_right _ hMC
  have heq : GSLit.fixedLayer M (zpowers b) = Jb := by
    rw [hfl]
    apply le_antisymm
    · rw [map_le_iff_le_comap]
      unfold pLayer
      refine sSup_le fun L hL => ?_
      set L' : Subgroup X := L.map Y.subtype with hL'def
      have hL'Y : L' ≤ Y := map_subtype_le _
      have hL'pc : IsPComponent 2 (L'.subgroupOf Y) := by
        change IsPComponent 2 ((L.map Y.subtype).comap Y.subtype)
        rw [comap_map_eq_self_of_injective Y.subtype_injective]
        exact hL
      have hperf : ⁅L', L'⁆ = L' := UnbalancedCorr.commutator_eq_of_isPComponent hL'Y hL'pc
      obtain ⟨-, hres, -⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L' Y hL'Y).mp hL'pc
      have hL'M : L' ≤ M := hL'Y.trans inf_le_left
      have hL'N : L' ≤ normalizer (M : Set X) := hL'M.trans le_normalizer
      have hL'b : L' ≤ centralizer ({b} : Set X) := hL'Y.trans inf_le_right
      have h1 : L' ≤ GH74.GLS.oPrimeResidualOf 2 L' := Sol78.le_oPrimeResidualOf le_rfl hres
      rw [Sol78.oPrimeResidualOf_eq_closure] at h1
      have h2 : L' ≤ Jb := by
        refine h1.trans ((closure_le _).mpr ?_)
        rintro y ⟨hy, k, hk⟩
        refine hmem y (hL'M hy) (mem_centralizer_singleton_iff.mp (hL'b hy)) ⟨k, hk⟩ ?_
        intro ω hω
        refine Finset.mem_compl.mpr fun hωb => (Perm.mem_support.mp hω) ?_
        have hfix := fix_support_rho_of_perfect hbN hb2 h4 hL'N hL'b hperf hy ω hωb
        have happ := hρ.apply_of_mem (by omega) ⟨y, hL'M hy⟩
        change ((θ ((⟨y, hL'M hy⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin n)) :
          Perm (Fin n)) ω = ω
        rw [← happ]
        exact hfix
      intro z hz
      exact h2 ⟨z, hz, rfl⟩
    · have hJbpc' : IsPComponent 2 (Jb.subgroupOf Y) :=
        CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJb hYC hJbpc
      have hle : Jb.subgroupOf Y ≤ pLayer ↥Y 2 := le_sSup hJbpc'
      intro x hx
      exact ⟨⟨x, hJb hx⟩, hle hx, rfl⟩
  rw [heq]
  exact ⟨hJb.trans hYC, hJbpc, ⟨χ⟩⟩

theorem alt_sup_eq_top {m : ℕ} (hm : Odd m) {S D : Finset (Fin m)} (hDS : D ⊆ S)
    (hSD : D.card + 2 ≤ S.card) {G : Subgroup (alternatingGroup (Fin m))}
    (hS : ∀ b : alternatingGroup (Fin m), (∀ ω ∉ S, (b : Perm (Fin m)) ω = ω) → b ∈ G)
    (hD : ∀ b : alternatingGroup (Fin m), (∀ ω ∈ D, (b : Perm (Fin m)) ω = ω) → b ∈ G) :
    G = ⊤ := by
  classical
  obtain ⟨x, hxS, hxD⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := D) (t := S) (by omega)
  obtain ⟨y, hyS, hyD⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := insert x D) (t := S)
    (lt_of_le_of_lt (Finset.card_insert_le _ _) (by omega))
  rw [Finset.mem_insert, not_or] at hyD
  have hxy : x ≠ y := Ne.symm hyD.1
  by_cases hSu : ∀ ω, ω ∈ S
  · exact eq_top_iff.mpr fun b _ => hS b fun ω hω => absurd (hSu ω) hω
  push Not at hSu
  obtain ⟨w, hwS⟩ := hSu
  have hwx : w ≠ x := fun h => hwS (h ▸ hxS)
  have hwy : w ≠ y := fun h => hwS (h ▸ hyS)
  have hstab : MulAction.stabilizer (alternatingGroup (Fin m))
      ((Sᶜ : Finset (Fin m)) : Set (Fin m)) ≤ G := by
    intro b hb
    obtain ⟨σD, σF, hb', h1, h2, -, -⟩ :=
      exists_split Sᶜ fun v => Sol78.apply_mem_iff_of_mem_stabilizer hb v
    have h1' : ∀ v ∈ S, σD v = v := fun v hv => h1 v (by simpa using hv)
    have h2' : ∀ v ∉ S, σF v = v := fun v hv => h2 v (Finset.mem_compl.mpr hv)
    have hsign : Perm.sign σD * Perm.sign σF = 1 := by
      rw [← map_mul, ← hb']
      exact Perm.mem_alternatingGroup.mp b.2
    have hc : ∀ v ∈ D, swap x y v = v := fun v hv =>
      swap_apply_of_ne_of_ne (fun h => hxD (h ▸ hv)) (fun h => hyD.2 (h ▸ hv))
    have hc' : ∀ v ∉ S, swap x y v = v := fun v hv =>
      swap_apply_of_ne_of_ne (fun h => hv (h ▸ hxS)) (fun h => hv (h ▸ hyS))
    rcases Int.units_eq_one_or (Perm.sign σD) with hD1 | hD1
    · have hF1 : Perm.sign σF = 1 := by rw [hD1, one_mul] at hsign; exact hsign
      have hσD : (⟨σD, Perm.mem_alternatingGroup.mpr hD1⟩ : alternatingGroup (Fin m)) ∈ G :=
        hD _ fun v hv => h1' v (hDS hv)
      have hσF : (⟨σF, Perm.mem_alternatingGroup.mpr hF1⟩ : alternatingGroup (Fin m)) ∈ G :=
        hS _ h2'
      have hbe : b = ⟨σD, Perm.mem_alternatingGroup.mpr hD1⟩ *
          ⟨σF, Perm.mem_alternatingGroup.mpr hF1⟩ := Subtype.ext hb'
      rw [hbe]
      exact mul_mem hσD hσF
    · have hF1 : Perm.sign σF = -1 := by
        rcases Int.units_eq_one_or (Perm.sign σF) with h | h
        · rw [hD1, h] at hsign
          exact absurd hsign (by decide)
        · exact h
      have hDc : Perm.sign (σD * swap x y) = 1 := by
        rw [map_mul, hD1, Perm.sign_swap hxy]
        decide
      have hcF : Perm.sign (swap x y * σF) = 1 := by
        rw [map_mul, hF1, Perm.sign_swap hxy]
        decide
      have hσD : (⟨σD * swap x y, Perm.mem_alternatingGroup.mpr hDc⟩ :
          alternatingGroup (Fin m)) ∈ G := by
        refine hD _ fun v hv => ?_
        change σD (swap x y v) = v
        rw [hc v hv, h1' v (hDS hv)]
      have hσF : (⟨swap x y * σF, Perm.mem_alternatingGroup.mpr hcF⟩ :
          alternatingGroup (Fin m)) ∈ G := by
        refine hS _ fun v hv => ?_
        change swap x y (σF v) = v
        rw [h2' v hv, hc' v hv]
      have hbe : b = ⟨σD * swap x y, Perm.mem_alternatingGroup.mpr hDc⟩ *
          ⟨swap x y * σF, Perm.mem_alternatingGroup.mpr hcF⟩ := by
        apply Subtype.ext
        change (b : Perm (Fin m)) = σD * swap x y * (swap x y * σF)
        rw [hb', mul_assoc, ← mul_assoc (swap x y), swap_mul_self, one_mul]
      rw [hbe]
      exact mul_mem hσD hσF
  have hb₀A : swap w x * swap w y ∈ alternatingGroup (Fin m) := by
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hwx, Perm.sign_swap hwy]
    decide
  have hb₀G : (⟨swap w x * swap w y, hb₀A⟩ : alternatingGroup (Fin m)) ∈ G := by
    refine hD _ fun v hv => ?_
    have hvS := hDS hv
    have hvw : v ≠ w := fun h => hwS (h ▸ hvS)
    have hvx : v ≠ x := fun h => hxD (h ▸ hv)
    have hvy : v ≠ y := fun h => hyD.2 (h ▸ hv)
    change (swap w x * swap w y) v = v
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hvw hvy, swap_apply_of_ne_of_ne hvw hvx]
  have hb₀S : (⟨swap w x * swap w y, hb₀A⟩ : alternatingGroup (Fin m)) ∉
      MulAction.stabilizer (alternatingGroup (Fin m)) ((Sᶜ : Finset (Fin m)) : Set (Fin m)) := by
    intro h
    have h1 := (Sol78.apply_mem_iff_of_mem_stabilizer h w).mpr (Finset.mem_compl.mpr hwS)
    change (swap w x * swap w y) w ∈ Sᶜ at h1
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hwy) (Ne.symm hxy)]
      at h1
    exact (Finset.mem_compl.mp h1) hyS
  have hco := alternatingGroup.isCoatom_stabilizer (α := Fin m)
    (s := ((Sᶜ : Finset (Fin m)) : Set (Fin m))) ⟨w, by simpa using hwS⟩ ⟨x, by simpa using hxS⟩
    (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      intro h
      obtain ⟨k, hk⟩ := hm
      omega)
  exact hco.2 _ (lt_of_le_of_ne hstab fun h => hb₀S (h ▸ hb₀G))

theorem le_of_map_eq_top [Finite X] {N H : Subgroup X} {m : ℕ}
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m))
    (hOH : (pPrimeCore 2 ↥N).map N.subtype ≤ H)
    (hY : (H.subgroupOf N).map (θN.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥N))) = ⊤) :
    N ≤ H := by
  set π : ↥N →* alternatingGroup (Fin m) :=
    θN.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥N)) with hπdef
  intro x hx
  obtain ⟨y, hy, hyx⟩ : π ⟨x, hx⟩ ∈ (H.subgroupOf N).map π := by rw [hY]; exact mem_top _
  have h1 : π (y⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have h2 : y⁻¹ * ⟨x, hx⟩ ∈ pPrimeCore 2 ↥N := by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ θN.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have h3 := mul_mem (show (y : X) ∈ H from hy) (hOH ⟨_, h2, rfl⟩)
  simpa using h3

theorem exists_fixedLayer_coreQuot_equiv [Finite X] {J E : Subgroup X}
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) (hE : E ≤ UnbalancedLayer.coreActionKernel J)
    (hE2 : IsPGroup 2 E) :
    ∃ Φ : ↥(GSLit.fixedLayer J E) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer J E) ≃*
        ↥J ⧸ pPrimeCore 2 ↥J,
      ∀ (x : ↥(GSLit.fixedLayer J E)) (hx : (x : X) ∈ J),
        Φ (x : ↥(GSLit.fixedLayer J E) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer J E)) =
          ((⟨x, hx⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JE := GSLit.fixedLayer J E with hJE
  have hJEJ : JE ≤ J := (GSLit.fixedLayer_le_inf J E).trans inf_le_left
  obtain ⟨hsup, hcore⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq hE hE2
  set f : ↥JE →* ↥J ⧸ pPrimeCore 2 ↥J :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp (inclusion hJEJ) with hfdef
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have hj : (j : X) ∈ ((JE ⊔ (pPrimeCore 2 ↥J).map J.subtype : Subgroup X) : Set X) := by
      rw [hsup]
      exact j.2
    have hnorm : JE ≤ normalizer (((pPrimeCore 2 ↥J).map J.subtype : Subgroup X) : Set X) :=
      fun y hy => le_normalizer_pPrimeCore (le_normalizer (hJEJ hy))
    rw [coe_mul_of_left_le_normalizer_right _ _ hnorm] at hj
    obtain ⟨a, ha, o, ⟨o', ho', rfl⟩, hao⟩ := hj
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hj' : j = inclusion hJEJ ⟨a, ha⟩ * o' := Subtype.ext hao.symm
    rw [hj', inv_mul_cancel_left]
    exact ho'
  have hker : pPrimeCore 2 ↥JE = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have h1 : (x : X) ∈ (pPrimeCore 2 ↥JE).map JE.subtype := ⟨x, hx, rfl⟩
      rw [hcore] at h1
      obtain ⟨y, hy, hyx⟩ := (mem_inf.mp h1).2
      have hy' : y = inclusion hJEJ x := Subtype.ext hyx
      rw [← hy']
      exact hy
    · intro hx
      have h1 : (x : X) ∈ JE ⊓ (pPrimeCore 2 ↥J).map J.subtype := ⟨x.2, ⟨_, hx, rfl⟩⟩
      rw [← hcore] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hy' : y = x := Subtype.ext hyx
      rw [← hy']
      exact hy
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun x hx => rfl⟩

theorem exists_rho_ne_one [Finite X] {M K : Subgroup X} {r : ℕ} (hr : 4 ≤ r)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θ ρ) (hKM : K ≤ M)
    (hK : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ x : ↥K, ρ ⟨x, (hKM.trans le_normalizer) x.2⟩ ≠ 1 := by
  obtain ⟨q, hq⟩ := exists_ne (1 : ↥K ⧸ pPrimeCore 2 ↥K)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨x, fun h => hq ?_⟩
  have h1 : ((θ ((⟨x, hKM x.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin r)) :
      Perm (Fin r)) = 1 := by
    rw [← hρ.apply_of_mem hr ⟨x, hKM x.2⟩]
    exact h
  have h2 : θ ((⟨x, hKM x.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := Subtype.ext h1
  rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h2
  have h3 : (x : X) ∈ K ⊓ (pPrimeCore 2 ↥M).map M.subtype := ⟨x.2, ⟨_, h2, rfl⟩⟩
  obtain ⟨y, hy, hyx⟩ := inf_pPrimeCore_le hKM h3
  have hy' : y = x := Subtype.ext hyx
  rw [QuotientGroup.eq_one_iff, ← hy']
  exact hy

namespace SwapP2

theorem claimA_of_inputs (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) : ClaimA := by
  intro X _ _ _ t J n e E D M hS hn F hFJ hF DF hDF hFs f hfF hf1
  obtain ⟨θ⟩ := hS.alt
  exact hS.sig.centralizer_le_of_mem_four_swap h33 h35 hPump hN1 hn hS.cent hS.le hS.pc hS.swap
    hS.diag θ hS.small hFJ hF hDF hFs hfF hf1

theorem pump_holds : Pump := by
  intro X _ _ _ t J n e E D M hs e₀ F DF r hd he₀H
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
  obtain ⟨π, hπ⟩ := S.exists_perm_compat_of_swap hs.cent hs.le hs.pc hs.swap hs.diag hρ
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀N : e₀ ∈ normalizer (M : Set X) := hJN he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [hπ e₀ he₀J he₀N, Perm.card_support_conj]
    exact S.card_support_coreImage_E hd.e₀E hd.e₀1
  obtain ⟨hAle, hApc, ⟨χA⟩⟩ :=
    fixedLayer_facts_of_perm hs.le hs.pc hρ he₀N he₀2 he₀4.le (by omega)
  have hHe : Hn E ⊓ centralizer ({e₀} : Set X) = centralizer ({e₀} : Set X) :=
    inf_eq_right.mpr he₀H
  rw [hHe] at hAle hApc
  set A := GSLit.fixedLayer M (zpowers e₀) with hAdef
  obtain ⟨-, -, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAle).mp hApc
  have hAsub : (A.subgroupOf (centralizer ({e₀} : Set X))).IsSubnormal := hApc.choose_spec.2.1
  have hAM : A ≤ M := (GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hre₀ : r ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀
  have hrA : r ∈ normalizer (A : Set X) := by
    refine GSLit.mem_normalizer_fixedLayer hrK.1 (centralizer_le_normalizer _ ?_)
    rw [centralizer_zpowers_eq' e₀]
    exact hre₀
  have hrKA : r ∈ UnbalancedLayer.coreActionKernel A := mem_coreActionKernel_of_le hAM hrK hrA
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hArpc := GSLit.fixedLayer_isPComponent hAle hAsub (zpowers_le.mpr hre₀)
    (zpowers_le.mpr hrKA) hR2 hAq
  rw [centralizer_zpowers_eq' r, inf_comm (centralizer ({e₀} : Set X))] at hArpc
  have hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) := by
    have h1 := GSLit.fixedLayer_le_inf A (zpowers r)
    rw [centralizer_zpowers_eq' r] at h1
    exact le_inf (h1.trans inf_le_right) ((h1.trans inf_le_left).trans hAle)
  have hcard : Fintype.card ↥((ρ ⟨e₀, he₀N⟩).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, he₀4]
  obtain ⟨ψ⟩ := fixedLayer_coreQuot_equiv hAq (zpowers_le.mpr hrKA) hR2
  refine ⟨⟨ψ.trans (χA.trans (Equiv.altCongrHom (Fintype.equivFinOfCardEq hcard)))⟩,
    ⟨hArle, hArpc⟩, ?_⟩
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  obtain ⟨N₁, hN₁le, hN₁pc, hcover, hlayer⟩ := exists_pump_in he₀r he₀o hArle hArpc
  exact ⟨N₁, ⟨hN₁le, hN₁pc, hcover, hlayer⟩⟩

theorem le_of_exact [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X} {N₁ : Subgroup X}
    (hs : Setting t J n e E D M) (hn : 11 ≤ n) (hd : Data t J n e E D M e₀ F DF r)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (hP : PumpData M e₀ r N₁) (hfix : conjBy N₁ e₀ = N₁)
    (hside : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M)
    {m : ℕ} (hmo : Odd m) (hkm : n - 4 ≤ m)
    (θN : ↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m)) : N₁ ≤ Hn E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  have hm6 : m ≠ 6 := by
    obtain ⟨a, ha⟩ := hmo
    omega
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
  obtain ⟨π, hπ⟩ := S.exists_perm_compat_of_swap hs.cent hs.le hs.pc hs.swap hs.diag hρ
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀N : e₀ ∈ normalizer (M : Set X) := hJN he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [hπ e₀ he₀J he₀N, Perm.card_support_conj]
    exact S.card_support_coreImage_E hd.e₀E hd.e₀1
  obtain ⟨hAle, hApc, ⟨χA⟩⟩ :=
    fixedLayer_facts_of_perm hs.le hs.pc hρ he₀N he₀2 he₀4.le (by omega)
  set A := GSLit.fixedLayer M (zpowers e₀) with hAdef
  have hAM : A ≤ M := (GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left
  have hAe : A ≤ centralizer ({e₀} : Set X) := hAle.trans inf_le_right
  have hAMe : A ≤ M ⊓ centralizer ({e₀} : Set X) := le_inf hAM hAe
  have hApcM : IsPComponent 2 (A.subgroupOf (M ⊓ centralizer ({e₀} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hAMe (inf_le_inf_right _ hs.le) hApc
  obtain ⟨-, hAres, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAMe).mp hApcM
  have hAperf : ⁅A, A⁆ = A := UnbalancedCorr.commutator_eq_of_isPComponent hAMe hApcM
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hre₀ : r ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀
  have hrA : r ∈ normalizer (A : Set X) := by
    refine GSLit.mem_normalizer_fixedLayer hrK.1 (centralizer_le_normalizer _ ?_)
    rw [centralizer_zpowers_eq' e₀]
    exact hre₀
  have hrKA : r ∈ UnbalancedLayer.coreActionKernel A := mem_coreActionKernel_of_le hAM hrK hrA
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hArA : fixA M e₀ r ≤ A := (GSLit.fixedLayer_le_inf A (zpowers r)).trans inf_le_left
  obtain ⟨Φ, hΦ⟩ := exists_fixedLayer_coreQuot_equiv hAq (zpowers_le.mpr hrKA) hR2
  have hcardA : Fintype.card ↥((ρ ⟨e₀, he₀N⟩).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, he₀4]
  obtain ⟨τM, hτM, ψM, hψM⟩ := exists_image_equiv (M := M) (Je := A) (by omega) (by omega)
    (by omega) θ hρ (hAM.trans le_normalizer) hAres hAperf hcardA χA
    (exists_rho_ne_one (by omega) hρ hAM (LocalCores.isQuasisimple_nontrivial hAq))
    (Or.inr ⟨e₀, he₀N, he₀2, hAM, hAe, hApcM⟩)
  have he₀N₁ : e₀ ∈ normalizer (N₁ : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
  obtain ⟨ρN, hρN⟩ := exists_isPermAction (M := N₁) (by omega) hm6 θN
  have hArN : fixA M e₀ r ≤ N₁ := by
    have h1 := hP.cover
    rwa [hfix, sup_idem] at h1
  have hlayer : IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X))) := by
    have h1 := hP.layer
    rwa [hfix, sup_idem] at h1
  have hAre : fixA M e₀ r ≤ centralizer ({e₀} : Set X) := hArA.trans hAe
  have hArY : fixA M e₀ r ≤ N₁ ⊓ centralizer ({e₀} : Set X) := le_inf hArN hAre
  obtain ⟨-, hArres, hArq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hArY).mp hlayer
  have hArperf : ⁅fixA M e₀ r, fixA M e₀ r⁆ = fixA M e₀ r :=
    UnbalancedCorr.commutator_eq_of_isPComponent hArY hlayer
  obtain ⟨τ', hτ', ψN, hψN⟩ := exists_image_equiv (M := N₁) (Je := fixA M e₀ r) (k := n - 4)
    (by omega) hkm hm6 θN hρN (hArN.trans le_normalizer) hArres hArperf hcardA (Φ.trans χA)
    (exists_rho_ne_one (by omega) hρN hArN (LocalCores.isQuasisimple_nontrivial hArq))
    (Or.inr ⟨e₀, he₀N₁, he₀2, hArN, hAre, hlayer⟩)
  obtain ⟨f₁, -, -, hf₁F, -, -, hf₁1, -, -, -, -, -⟩ := exists_three_of_klein hd.Fk
  obtain ⟨a₁, ha₁, hfaN, hfaM⟩ := hside f₁ hf₁F
  have ha₁N : a₁ ∈ N₁ := hArN ha₁
  have ha₁A : a₁ ∈ A := hArA ha₁
  have hf₁J : f₁ ∈ J := hd.FJ hf₁F
  have hf₁M : f₁ ∈ normalizer (M : Set X) := hJN hf₁J
  have hf₁2 : f₁ * f₁ = 1 := by rw [← sq]; exact (card_sq_of_klein hd.Fk).2 f₁ hf₁F
  have hf₁N : f₁ ∈ normalizer (N₁ : Set X) := by
    have h1 : f₁ = (f₁ * a₁⁻¹) * a₁ := by group
    rw [h1]
    exact mul_mem hfaN.1 (le_normalizer ha₁N)
  have hρfa : ρ ⟨f₁, hf₁M⟩ = ρ ⟨a₁, le_normalizer (hAM ha₁A)⟩ := by
    have h1 := hρ.eq_one_of_mem_coreActionKernel (by omega) hfaM
    have h2 : (⟨f₁ * a₁⁻¹, hfaM.1⟩ : ↥(normalizer (M : Set X))) =
        ⟨f₁, hf₁M⟩ * (⟨a₁, le_normalizer (hAM ha₁A)⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hρNfa : ρN ⟨f₁, hf₁N⟩ = ρN ⟨a₁, le_normalizer ha₁N⟩ := by
    have h1 := hρN.eq_one_of_mem_coreActionKernel (by omega) hfaN
    have h2 : (⟨f₁ * a₁⁻¹, hfaN.1⟩ : ↥(normalizer (N₁ : Set X))) =
        ⟨f₁, hf₁N⟩ * (⟨a₁, le_normalizer ha₁N⟩ : ↥(normalizer (N₁ : Set X)))⁻¹ := rfl
    rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hf₁4 : (ρ ⟨f₁, hf₁M⟩).support.card = 4 := by
    rw [hπ f₁ hf₁J hf₁M, Perm.card_support_conj]
    exact card_support_coreImage_of_four e hf₁J hf₁2 hf₁1 hd.DFc (hd.Fs ⟨f₁, hf₁J⟩ hf₁F)
  obtain ⟨φM, hφM⟩ := exists_fixAlt_equiv τM
  have hβ : Fintype.card ↥(τM.supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτM]
  set q : ↥A ⧸ pPrimeCore 2 ↥A := ((⟨a₁, ha₁A⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) with hqdef
  have hq : Φ (((⟨a₁, ha₁⟩ : ↥(fixA M e₀ r)) : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r))) =
      q := hΦ ⟨a₁, ha₁⟩ ha₁A
  set ψ : alternatingGroup ↥(τM.supportᶜ : Finset (Fin n)) ≃* fixAlt τ' :=
    (φM.trans ψM.symm).trans (Φ.symm.trans ψN) with hψdef
  have hψg : ψ (φM.symm (ψM q)) = ψN (((⟨a₁, ha₁⟩ : ↥(fixA M e₀ r)) :
      ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r))) := by
    rw [hψdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply, ← hq, MulEquiv.symm_apply_apply]
  have hsupp := card_support_of_le_fixAlt (k := n - 4) (by omega) hτ' (le_refl (fixAlt τ')) hβ ψ
    (φM.symm (ψM q))
  rw [hψg, hψN ⟨a₁, ha₁⟩] at hsupp
  have hσ4 : (ρN ⟨f₁, hf₁N⟩).support.card = 4 := by
    rw [hρNfa]
    refine hsupp.trans ?_
    rw [← card_support_ofSubtype, ← hφM, MulEquiv.apply_symm_apply, hqdef, hψM ⟨a₁, ha₁A⟩,
      ← hρfa, hf₁4]
  have hσS : (ρN ⟨f₁, hf₁N⟩).support ⊆ τ'.supportᶜ := by
    rw [hρNfa, ← hψN ⟨a₁, ha₁⟩]
    exact mem_fixAlt.mp (ψN _).2
  have hScard : (τ'.supportᶜ).card = n - 4 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  set πN : ↥N₁ →* alternatingGroup (Fin m) :=
    θN.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥N₁)) with hπNdef
  have hOH : (pPrimeCore 2 ↥N₁).map N₁.subtype ≤ Hn E :=
    (pPrimeCore_le_of_isPComponent hP.le hP.pc).trans hOr
  refine le_of_map_eq_top θN hOH (alt_sup_eq_top hmo hσS (by omega) ?_ ?_)
  ·
    intro b hb
    have hbF : b ∈ fixAlt τ' := by
      rw [mem_fixAlt]
      intro ω hω
      by_contra hωF
      exact (Perm.mem_support.mp hω) (hb ω hωF)
    obtain ⟨q', hq'⟩ := ψN.surjective ⟨b, hbF⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q'
    have hxH : (x : X) ∈ Hn E := hs.le (hAM (hArA x.2))
    refine ⟨⟨x, hArN x.2⟩, hxH, Subtype.ext ?_⟩
    have h1 := hψN x
    rw [hq'] at h1
    rw [h1]
    exact (hρN.apply_of_mem (by omega) ⟨x, hArN x.2⟩).symm
  ·
    intro b hb
    have hdisj : Perm.Disjoint (b : Perm (Fin m)) (ρN ⟨f₁, hf₁N⟩) := by
      intro ω
      by_cases hω : ω ∈ (ρN ⟨f₁, hf₁N⟩).support
      · exact Or.inl (hb ω hω)
      · exact Or.inr (Perm.notMem_support.mp hω)
    obtain ⟨x, hxC, hxb⟩ := hρN.exists_lift hf₁N hf₁2 (b := b) hdisj.commute.eq
    exact ⟨x, hFH f₁ hf₁F hf₁1 hxC, hxb⟩

theorem conjBy_conjBy_of_mul_self (L : Subgroup X) {g : X} (hg : g * g = 1) :
    conjBy (conjBy L g) g = L := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hid : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom : X →* X) =
      MonoidHom.id X := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply, hinv]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg]; group
  show (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = L
  rw [Subgroup.map_map, hid, Subgroup.map_id]

theorem eq_or_eq_of_pumpData [Finite X] {M : Subgroup X} {e₀ r : X} {N₁ N : Subgroup X}
    (he₀r : e₀ ∈ centralizer ({r} : Set X)) (he₀2 : e₀ * e₀ = 1) (hP : PumpData M e₀ r N₁)
    (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hAN : fixA M e₀ r ≤ N ⊔ conjBy N e₀) : N = N₁ ∨ N = conjBy N₁ e₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe : fixA M e₀ r ≤ centralizer ({e₀} : Set X) := by
    have h1 := (((GSLit.fixedLayer_le_inf (GSLit.fixedLayer M (zpowers e₀)) (zpowers r)).trans
      inf_le_left).trans (GSLit.fixedLayer_le_inf M (zpowers e₀))).trans inf_le_right
    rwa [centralizer_zpowers_eq'] at h1
  have hAY : fixA M e₀ r ≤ (N₁ ⊔ conjBy N₁ e₀) ⊓ centralizer ({e₀} : Set X) :=
    le_inf hP.cover hAe
  have hperf := UnbalancedCorr.commutator_eq_of_isPComponent hAY hP.layer
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hAY).mp hP.layer
  obtain ⟨h₁, h₁p⟩ := isPComponent_conj hP.le hP.pc he₀r
  obtain ⟨h₂, h₂p⟩ := isPComponent_conj hNC hNpc he₀r
  rcases exists_eq_of_le_sup_sup hP.le hP.pc h₁ h₁p hNC hNpc h₂ h₂p hperf
      (LocalCores.isQuasisimple_nontrivial hq) hP.cover hAN with h | h | h | h
  · exact Or.inl h.symm
  · right
    rw [h, conjBy_conjBy_of_mul_self N he₀2]
  · exact Or.inr h.symm
  · exact Or.inl (Subgroup.map_injective (MulAut.conj e₀).injective h).symm

theorem pumpLe_of_inputs (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) : PumpLe := by
  intro X _ _ _ t J n e E D M hs hn e₀ F DF r hd he₀H hOr N₁ hP hfix hside
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hFH := claimA_of_inputs h33 h35 hPump hN1 X t J n e E D M hs hn F hd.FJ hd.Fk DF hd.DFc
    hd.Fs
  obtain ⟨⟨χr⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({r} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top S.kProper (centralizer_ne_top_of_ne_one S.nonab hd.r1)
  have hkodd : Odd (n - 4) := by
    obtain ⟨a, ha⟩ := S.pair.2.1
    exact ⟨a - 2, by omega⟩
  obtain ⟨N, hNC, hNpc, hAN, -, htype⟩ :=
    pump_type_in hPump hK he₀r he₀o hArle hArpc hkodd (by omega) χr
  have hNN₁ : N = N₁ := by
    rcases eq_or_eq_of_pumpData he₀r he₀2 hP hNC hNpc hAN with h | h
    · exact h
    · rw [h, hfix]
  subst hNN₁
  rcases htype with ⟨-, ⟨m, hmo, hkm, ⟨eN⟩⟩ | ⟨h7, -⟩⟩ | ⟨hne, -⟩
  · have hT : zpowers r ≠ ⊥ := fun h => hd.r1 (zpowers_eq_bot.mp h)
    have hCr : centralizer ((zpowers r : Subgroup X) : Set X) = centralizer ({r} : Set X) :=
      centralizer_zpowers_eq' r
    have hNC' : N ≤ centralizer ((zpowers r : Subgroup X) : Set X) := by
      rw [hCr]
      exact hNC
    have hNpc' : IsPComponent 2
        (N.subgroupOf (centralizer ((zpowers r : Subgroup X) : Set X))) := by
      rw [hCr]
      exact hNpc
    have hZ := hN1 X S.nonab S.kProper S.unbal S.notU (zpowers r) m N hT
      (isPGroup_zpowers_of_mul_self hd.r2) hmo (by omega) hNC' hNpc' ⟨eN⟩
    exact le_of_exact hs (by omega) hd hOr hFH hP hfix hside hmo hkm
      ((QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eN)
  · omega
  · exact absurd hfix hne

theorem dataExist_holds : DataExist := by
  intro X _ _ _ t J n e E D M hs e₀ he₀E he₀1
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by omega) (by omega) e
  have hρJe : ρJ ⟨e₀, le_normalizer he₀J⟩ = coreImage e he₀J :=
    hρJ.apply_of_mem (by omega) ⟨e₀, he₀J⟩
  have hsuppJ : (ρJ ⟨e₀, le_normalizer he₀J⟩).support = D := by
    rw [hρJe]
    exact S.support_coreImage_E he₀E he₀1
  set Fx : Finset (Fin n) := (ρJ ⟨e₀, le_normalizer he₀J⟩).supportᶜ with hFxdef
  obtain ⟨Jb, hJb, -, -, -, χ, hχ⟩ := exists_fixed_component_of_perm S.pair.1.2.1
    S.pair.1.2.2.1 hρJ (le_normalizer he₀J) he₀2 (by rw [hsuppJ, S.card]; omega)
  have hcard : Fintype.card ↥Fx = n - 4 := by
    rw [Fintype.card_coe, hFxdef, Finset.card_compl, Fintype.card_fin, hsuppJ, S.card]
  set ε : ↥Fx ≃ Fin (n - 4) := Fintype.equivFinOfCardEq hcard with hεdef
  set f : ↥Jb →* alternatingGroup (Fin (n - 4)) :=
    (ε.altCongrHom.toMonoidHom.comp χ.toMonoidHom).comp (QuotientGroup.mk' (pPrimeCore 2 ↥Jb))
    with hfdef
  have hfs : Function.Surjective f :=
    ε.altCongrHom.surjective.comp (χ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : f.ker = pPrimeCore 2 ↥Jb := by
    ext x
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ε.altCongrHom.injective, map_eq_one_iff _ χ.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨F, hFJb, hFk, D', hD'4, hD'⟩ := exists_four_subgroup_of_surjective (by omega) f hfs
    (by rw [hker]; exact Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  set DF : Finset (Fin n) :=
    D'.map (ε.symm.toEmbedding.trans (Function.Embedding.subtype _)) with hDFdef
  have hDFc : DF.card = 4 := by rw [hDFdef, Finset.card_map, hD'4]
  have hDFx : DF ⊆ Fx := by
    intro ω hω
    rw [hDFdef, Finset.mem_map] at hω
    obtain ⟨i, -, rfl⟩ := hω
    exact (ε.symm i).2
  have hdisj : Disjoint D DF := by
    rw [Finset.disjoint_left]
    intro ω hωD hωDF
    have h1 := hDFx hωDF
    rw [hFxdef, Finset.mem_compl, hsuppJ] at h1
    exact h1 hωD
  have hFs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
    intro x hxF ω hω
    set xb : ↥Jb := ⟨x, hFJb hxF⟩ with hxbdef
    have h1 := hχ xb x.2
    have h2 : coreImage e x.2 =
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) := rfl
    rw [← h2, ← h1]
    by_cases hωF : ω ∈ Fx
    · have hi : ε ⟨ω, hωF⟩ ∉ D' := by
        intro hi
        apply hω
        rw [hDFdef, Finset.mem_map]
        exact ⟨ε ⟨ω, hωF⟩, hi, by simp⟩
      have h3 := hD' xb hxF (ε ⟨ω, hωF⟩) hi
      simp only [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
        Equiv.altCongrHom_apply_coe] at h3
      change ε.permCongr _ _ = _ at h3
      rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at h3
      rw [Perm.ofSubtype_apply_of_mem _ hωF, ε.injective h3]
    · exact Perm.ofSubtype_apply_of_not_mem _ hωF
  have hFe : F ≤ centralizer ({e₀} : Set X) := hFJb.trans (hJb.trans inf_le_right)
  have hFJ : F ≤ J := hFJb.trans (hJb.trans inf_le_left)
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtt : conjBy (conjBy M t) t = M := conjBy_conjBy_of_mul_self M ht2
  have hne' : conjBy (conjBy M t) t ≠ conjBy M t := by
    rw [hMtt]
    exact Ne.symm hs.swap
  have hJM' : J ≤ conjBy M t ⊔ conjBy (conjBy M t) t := by
    rw [hMtt, sup_comm]
    exact hs.diag
  have hJNt : J ≤ normalizer ((conjBy M t : Subgroup X) : Set X) :=
    le_normalizer_of_swap htH hMtH hMtpc hne' hJM'
  obtain ⟨θ⟩ := hs.alt
  set θt : ↥(conjBy M t) ⧸ pPrimeCore 2 ↥(conjBy M t) ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (M.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)).symm.trans θ with hθtdef
  obtain ⟨ρt, hρt⟩ := exists_isPermAction (M := conjBy M t) (by omega) (by omega) θt
  obtain ⟨πt, hπt⟩ := S.exists_perm_compat_of_swap hs.cent hMtH hMtpc hne' hJM' hρt
  have he₀Nt : e₀ ∈ normalizer ((conjBy M t : Subgroup X) : Set X) := hJNt he₀J
  have hρt4 : (ρt ⟨e₀, he₀Nt⟩).support.card = 4 := by
    rw [hπt e₀ he₀J he₀Nt, Perm.card_support_conj]
    exact S.card_support_coreImage_E he₀E he₀1
  have he₀CF : e₀ ∈ centralizer (F : Set X) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.mp (hFe hh)
  have hF2 : IsPGroup 2 F :=
    IsPGroup.of_card (n := 2) (by rw [(card_sq_of_klein hFk).1]; norm_num)
  set B : Subgroup X := zpowers e₀ ⊔ F with hBdef
  have hB2 : IsPGroup 2 B := IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self he₀2)
    hF2 (zpowers_le.mpr (centralizer_le_normalizer _ he₀CF))
  have hBN : B ≤ normalizer ((conjBy M t : Subgroup X) : Set X) :=
    (sup_le (zpowers_le.mpr he₀J) hFJ).trans hJNt
  have hBe : B ≤ centralizer ({e₀} : Set X) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) hFe
  have hJperf : ⁅J, J⁆ = J :=
    UnbalancedCorr.commutator_eq_of_isPComponent S.pair.1.2.1 S.pair.1.2.2.1
  have hbA : ρt ⟨e₀, he₀Nt⟩ ∈ alternatingGroup (Fin n) :=
    IsPermAction.mem_alternatingGroup_of_perfect hJNt hJperf he₀J
  set b : alternatingGroup (Fin n) := ⟨ρt ⟨e₀, he₀Nt⟩, hbA⟩ with hbdef
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    change ρt ⟨e₀, he₀Nt⟩ ^ 2 = 1
    rw [← map_pow, sq, show (⟨e₀, he₀Nt⟩ : ↥(normalizer ((conjBy M t : Subgroup X) : Set X))) *
      ⟨e₀, he₀Nt⟩ = 1 from Subtype.ext he₀2, map_one]
  obtain ⟨x, hxB, hxb⟩ := hρt.exists_lift_of_isPGroup hBN hB2 (b := b) (fun g hg => by
    change ρt ⟨e₀, he₀Nt⟩ * ρt ⟨g, hBN hg⟩ = ρt ⟨g, hBN hg⟩ * ρt ⟨e₀, he₀Nt⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hBe hg)).symm)
  have hx2 : x ^ 2 ∈ pPrimeCore 2 ↥(conjBy M t) := by
    have h1 : θt ((x ^ 2 : ↥(conjBy M t)) : ↥(conjBy M t) ⧸ pPrimeCore 2 ↥(conjBy M t)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, hxb, hb2]
    rwa [map_eq_one_iff _ θt.injective, QuotientGroup.eq_one_iff] at h1
  have hodd : Odd (orderOf (x ^ 2)) := by
    have h1 : orderOf (⟨x ^ 2, hx2⟩ : ↥(pPrimeCore 2 ↥(conjBy M t))) ∣
        Nat.card (pPrimeCore 2 ↥(conjBy M t)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  set y : ↥(conjBy M t) := x ^ orderOf (x ^ 2) with hydef
  have hy2 : y * y = 1 := by
    rw [hydef, ← pow_add, ← two_mul, pow_mul, pow_orderOf_eq_one]
  have hyb : θt (y : ↥(conjBy M t) ⧸ pPrimeCore 2 ↥(conjBy M t)) = b := by
    obtain ⟨k, hk⟩ := hodd
    rw [hydef, QuotientGroup.mk_pow, map_pow, hxb, hk, pow_succ, pow_mul, hb2, one_pow, one_mul]
  have hyN : (y : X) ∈ normalizer ((conjBy M t : Subgroup X) : Set X) := le_normalizer y.2
  have hρy : ρt ⟨y, hyN⟩ = ρt ⟨e₀, he₀Nt⟩ := by
    rw [hρt.apply_of_mem (by omega) y, hyb]
  have hcomm : ∀ g ∈ B, (y : X) * g = g * y := by
    intro g hg
    have h1 : g * (x : X) = x * g := (mem_centralizer_iff.mp hxB) g hg
    have h2 : Commute g (x : X) := h1
    have h3 : Commute g ((x : X) ^ orderOf (x ^ 2)) := h2.pow_right _
    have h4 : ((y : ↥(conjBy M t)) : X) = (x : X) ^ orderOf (x ^ 2) := by
      rw [hydef, SubgroupClass.coe_pow]
    rw [h4]
    exact h3.eq.symm
  refine ⟨F, DF, (y : X), ⟨he₀E, he₀1, hFJ, hFk, hDFc, hFs, hdisj, hFe, y.2,
    congrArg Subtype.val hy2, ?_, hcomm e₀ (mem_sup_left (mem_zpowers e₀)), ?_, ?_⟩⟩
  · intro hy1
    have h1 : ρt ⟨e₀, he₀Nt⟩ = 1 := by
      rw [← hρy]
      have h2 : (⟨(y : X), hyN⟩ : ↥(normalizer ((conjBy M t : Subgroup X) : Set X))) = 1 :=
        Subtype.ext hy1
      rw [h2, map_one]
    rw [h1, Perm.support_one, Finset.card_empty] at hρt4
    exact absurd hρt4 (by norm_num)
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr (hcomm g (mem_sup_right hg)).symm
  · have hyeN : (y : X) * e₀⁻¹ ∈ normalizer ((conjBy M t : Subgroup X) : Set X) :=
      mul_mem hyN (inv_mem he₀Nt)
    refine hρt.mem_coreActionKernel hyeN ?_
    have h1 : (⟨(y : X) * e₀⁻¹, hyeN⟩ : ↥(normalizer ((conjBy M t : Subgroup X) : Set X))) =
        ⟨y, hyN⟩ * (⟨e₀, he₀Nt⟩ : ↥(normalizer ((conjBy M t : Subgroup X) : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_inv, hρy, mul_inv_cancel]

theorem signalizerSwapMemberNarrowInput_of_inputs (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hPS : PumpSide) (hPD : PumpDiag)
    (hres : SwapMemberResidue) : SignalizerSwapMemberNarrowInput :=
  signalizerSwapMemberNarrowInput_of_steps (claimA_of_inputs h33 h35 hPump hN1) dataExist_holds
    pump_holds hPS (pumpLe_of_inputs h33 h35 hPump hN1) hPD hres

end SwapP2

end CFSG.ComponentClassification.SolMax
