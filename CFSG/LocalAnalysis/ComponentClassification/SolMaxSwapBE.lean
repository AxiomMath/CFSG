module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

theorem false_of_diagonal (hs : Setting t J n e E D M) (hn : 11 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (n - 4)))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N : Subgroup X} (hNC : N ≤ centralizer ({r} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N ⊔ conjBy N e₀) (hdiag : conjBy N e₀ ≠ N)
    (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin (n - 4)))
    (hside : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r,
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N ⊔ conjBy N e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  set m := n - 4 with hmdef
  set Ar := fixA M e₀ r with hArdef
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  obtain ⟨hNxC, hNxpc⟩ := isPComponent_conj hNC hNpc he₀r
  have hNxK : conjBy N e₀ ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNxC hNpc hNxpc (Ne.symm hdiag)
  have hNKx : N ≤ UnbalancedLayer.coreActionKernel (conjBy N e₀) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNxC hNC hNxpc hNpc hdiag
  set Y := N ⊔ conjBy N e₀ with hYdef
  have hYN : Y ≤ normalizer (N : Set X) := sup_le le_normalizer (fun z hz => (hNxK hz).1)
  have hArN : Ar ≤ normalizer (N : Set X) := hcov.trans hYN
  have hArM : Ar ≤ M :=
    ((GSLit.fixedLayer_le_inf _ (zpowers r)).trans inf_le_left).trans
      ((GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left)
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := N) (by omega) (by omega) θN
  have hArperf : ⁅Ar, Ar⁆ = Ar := UnbalancedCorr.commutator_eq_of_isPComponent hArle hArpc
  obtain ⟨-, hArres, hArq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Ar _ hArle).mp hArpc
  have hArnt := LocalCores.isQuasisimple_nontrivial hArq
  have hne := exists_ne_one_of_pump hNC hNpc he₀r hcov (hArle.trans inf_le_right) hArperf hArnt
    (r := m) (by omega) hρ hArN
  obtain ⟨τ, hτk, ψ, hψ⟩ := exists_image_equiv (M := N) (Je := Ar) (k := m) (by omega) le_rfl
    (by omega) θN hρ hArN hArres hArperf (Fintype.card_fin m) χr hne (Or.inl rfl)
  have hτ1 : τ.support = ∅ := by
    have hsm : τ.support.card ≤ m := by
      have h1 := Finset.card_le_univ τ.support
      rwa [Fintype.card_fin] at h1
    rw [← Finset.card_eq_zero]
    omega
  have hsurj : ∀ σ : alternatingGroup (Fin m), ∃ z : ↥Ar, ρ ⟨z, hArN z.2⟩ = σ := by
    intro σ
    have hσ : σ ∈ fixAlt τ := by
      rw [mem_fixAlt, hτ1, Finset.compl_empty]
      exact Finset.subset_univ _
    obtain ⟨q, hq⟩ := ψ.surjective ⟨σ, hσ⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨z, by rw [← hψ z, hq]⟩
  have hYC : Y ≤ centralizer ({r} : Set X) := sup_le hNC hNxC
  have hYsub : (Y.subgroupOf (centralizer ({r} : Set X))).IsSubnormal := by
    rw [hYdef, subgroupOf_sup hNC hNxC]
    exact CFSG.GroupTheory.isSubnormal_sup hNpc.choose_spec.2.1 hNxpc.choose_spec.2.1
  have hOY : (pPrimeCore 2 ↥Y).map Y.subtype ≤ Hn E :=
    (pPrimeCore_map_le_of_isSubnormal hYC hYsub).trans hOr
  have hON : (pPrimeCore 2 ↥N).map N.subtype ≤ (pPrimeCore 2 ↥Y).map Y.subtype := by
    refine le_pPrimeCore_map ((map_subtype_le _).trans le_sup_left) (sup_le ?_ ?_) ?_
    · exact fun y hy => le_normalizer_pPrimeCore (le_normalizer hy)
    · exact fun y hy => le_normalizer_pPrimeCore (hNxK hy).1
    · rw [card_map_of_injective N.subtype_injective]
      exact pPrimeCore_coprime_card
  have hOYodd : Odd (Nat.card ↥((pPrimeCore 2 ↥Y).map Y.subtype)) := by
    rw [card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨f, -, -, hfF, -, -, hf1, -, -, -, -, -⟩ := exists_three_of_klein hd.Fk
  obtain ⟨a, ha, hfaY, -⟩ := hside f hfF
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hd.Fk).2 f hfF
  have haY : a ∈ Y := hcov ha
  have hfNY : f ∈ normalizer (Y : Set X) := by
    rw [show f = (f * a⁻¹) * a by group]
    exact mul_mem hfaY.1 (le_normalizer haY)
  set u := ρ ⟨a, hArN ha⟩ with hudef
  have hm5 : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_fin]; omega
  have := alternatingGroup.isSimpleGroup hm5
  obtain ⟨σ₀, hσ₀1, hσ₀u⟩ : ∃ σ₀ : alternatingGroup (Fin m), σ₀ ≠ 1 ∧
      (σ₀ : Perm (Fin m)) * u = u * σ₀ := by
    by_cases hu : u = 1
    · obtain ⟨σ₀, hσ₀⟩ := exists_ne (1 : alternatingGroup (Fin m))
      exact ⟨σ₀, hσ₀, by rw [hu, mul_one, one_mul]⟩
    · have huA : u ∈ alternatingGroup (Fin m) :=
        IsPermAction.mem_alternatingGroup_of_perfect hArN hArperf ha
      exact ⟨⟨u, huA⟩, fun h => hu (congrArg Subtype.val h), rfl⟩
  obtain ⟨q₀, hq₀⟩ := θN.surjective σ₀
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective q₀
  have hρy₀ : ρ ⟨y₀, le_normalizer y₀.2⟩ = σ₀ := by rw [hρ.apply_of_mem (by omega) y₀, hq₀]
  have hy₀Y : (y₀ : X) ∈ Y := mem_sup_left y₀.2
  have hc : a * y₀ * a⁻¹ * (y₀ : X)⁻¹ ∈ (pPrimeCore 2 ↥N).map N.subtype := by
    have hcN : a * y₀ * a⁻¹ * (y₀ : X)⁻¹ ∈ N :=
      mul_mem ((mem_normalizer_iff.mp (hArN ha) y₀).mp y₀.2) (inv_mem y₀.2)
    have h1 : ρ ⟨a * y₀ * a⁻¹ * (y₀ : X)⁻¹, le_normalizer hcN⟩ = 1 := by
      have e1 : (⟨a * y₀ * a⁻¹ * (y₀ : X)⁻¹, le_normalizer hcN⟩ : ↥(normalizer (N : Set X))) =
          ⟨a, hArN ha⟩ * ⟨y₀, le_normalizer y₀.2⟩ * (⟨a, hArN ha⟩)⁻¹ *
            (⟨y₀, le_normalizer y₀.2⟩)⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hρy₀, ← hudef]
      calc u * σ₀ * u⁻¹ * (σ₀ : Perm (Fin m))⁻¹ = σ₀ * u * u⁻¹ * (σ₀ : Perm (Fin m))⁻¹ := by
            rw [← hσ₀u]
        _ = 1 := by group
    rw [hρ.apply_of_mem (by omega) ⟨_, hcN⟩] at h1
    have h2 : θN ((⟨_, hcN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  have hgN : f * a⁻¹ ∈ normalizer (((pPrimeCore 2 ↥Y).map Y.subtype : Subgroup X) : Set X) :=
    le_normalizer_pPrimeCore hfaY.1
  have hg1 : (f * a⁻¹) * y₀ * (f * a⁻¹)⁻¹ * (y₀ : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hfaY)).2 (y₀ : X)⁻¹
      (inv_mem hy₀Y)
    rw [inv_inv, inv_inv] at h1
    have h2 := inv_mem h1
    rwa [show ((y₀ : X) * (f * a⁻¹) * (y₀ : X)⁻¹ * (f * a⁻¹)⁻¹)⁻¹ =
      (f * a⁻¹) * y₀ * (f * a⁻¹)⁻¹ * (y₀ : X)⁻¹ by group] at h2
  have hfy : f * y₀ * f⁻¹ * (y₀ : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    have h1 := (mem_normalizer_iff.mp hgN _).mp (hON hc)
    have h2 := mul_mem h1 hg1
    rwa [show (f * a⁻¹) * (a * y₀ * a⁻¹ * (y₀ : X)⁻¹) * (f * a⁻¹)⁻¹ *
      ((f * a⁻¹) * y₀ * (f * a⁻¹)⁻¹ * (y₀ : X)⁻¹) = f * y₀ * f⁻¹ * (y₀ : X)⁻¹ by group] at h2
  have hfo : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hf2) hf1
  have hx : ∀ w ∈ zpowers f, w * y₀ * w⁻¹ * (y₀ : X)⁻¹ ∈ (pPrimeCore 2 ↥Y).map Y.subtype := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have hk : f ^ k = 1 ∨ f ^ k = f := by
      rw [← zpow_mod_orderOf, hfo]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [Nat.cast_ofNat, h, zpow_zero]
      · right
        rw [Nat.cast_ofNat, h, zpow_one]
    rcases hk with h | h <;> rw [h]
    · simp
    · exact hfy
  obtain ⟨v, hv, hvf⟩ := exists_fixed_in_coset (isPGroup_zpowers_of_mul_self hf2) hOYodd
    (zpowers_le.mpr (le_normalizer_pPrimeCore hfNY))
    (le_normalizer_pPrimeCore (le_normalizer hy₀Y)) hx
  have hyvC : (y₀ : X) * v ∈ centralizer ({f} : Set X) := by
    have h1 := hvf f (mem_zpowers f)
    rw [mem_centralizer_singleton_iff]
    calc (y₀ : X) * v * f = (f * ((y₀ : X) * v) * f⁻¹) * f := by rw [h1]
      _ = f * ((y₀ : X) * v) := by group
  have hy₀H : (y₀ : X) ∈ Hn E := by
    have h3 := mul_mem (hFH f hfF hf1 hyvC) (inv_mem (hOY hv))
    rwa [mul_inv_cancel_right] at h3
  set πN : ↥N →* alternatingGroup (Fin m) :=
    θN.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥N)) with hπNdef
  have hπρ : ∀ x : ↥N, ((πN x : alternatingGroup (Fin m)) : Perm (Fin m)) =
      ρ ⟨x, le_normalizer x.2⟩ := fun x => (hρ.apply_of_mem (by omega) x).symm
  set I := ((Hn E).subgroupOf N).map πN with hIdef
  have hInorm : I.Normal := by
    refine ⟨fun i hi σ => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hi
    obtain ⟨z, hz⟩ := hsurj σ
    have hzy : (z : X) * y * (z : X)⁻¹ ∈ N := (mem_normalizer_iff.mp (hArN z.2) y).mp y.2
    have hzH : (z : X) ∈ Hn E := hs.le (hArM z.2)
    refine ⟨⟨_, hzy⟩, mul_mem (mul_mem hzH hy) (inv_mem hzH), ?_⟩
    apply Subtype.ext
    have e1 : (⟨(z : X) * y * (z : X)⁻¹, le_normalizer hzy⟩ : ↥(normalizer (N : Set X))) =
        ⟨z, hArN z.2⟩ * ⟨y, le_normalizer y.2⟩ * (⟨z, hArN z.2⟩)⁻¹ := rfl
    rw [hπρ, e1, map_mul, map_mul, map_inv, hz, ← hπρ y]
    rfl
  have hIne : I ≠ ⊥ := by
    intro hI
    have h1 : πN y₀ ∈ I := ⟨y₀, hy₀H, rfl⟩
    rw [hI, mem_bot] at h1
    change θN ((y₀ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 at h1
    rw [hq₀] at h1
    exact hσ₀1 h1
  have hItop : I = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal I).resolve_left hIne
  have hNH : N ≤ Hn E :=
    le_of_map_eq_top θN ((pPrimeCore_le_of_isPComponent hNC hNpc).trans hOr) hItop
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hrH : r ∈ Hn E := hMtH hd.rM
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M (Hn E) hs.le).mp hs.pc).2.2
  have hCr : centralizer ((zpowers r : Subgroup X) : Set X) = centralizer ({r} : Set X) :=
    centralizer_zpowers_eq' r
  have hMrpc := GSLit.fixedLayer_isPComponent hs.le hs.pc.choose_spec.2.1 (zpowers_le.mpr hrH)
    (zpowers_le.mpr hrK) hR2 hMq
  rw [hCr] at hMrpc
  have hMrle := GSLit.fixedLayer_le_inf M (zpowers r)
  rw [hCr] at hMrle
  have hMrY : GSLit.fixedLayer M (zpowers r) ≤ Hn E ⊓ centralizer ({r} : Set X) :=
    le_inf ((hMrle.trans inf_le_left).trans hs.le) (hMrle.trans inf_le_right)
  have hArMC : Ar ≤ M ⊓ centralizer ((zpowers r : Subgroup X) : Set X) := by
    rw [hCr]
    exact le_inf hArM (hArle.trans inf_le_left)
  have hArMr : Ar ≤ GSLit.fixedLayer M (zpowers r) :=
    le_fixedLayer_of_primeResidual hMq (zpowers_le.mpr hrK) hR2 hArMC hArres
  have he₀H' : e₀ ∈ Hn E := he₀H (mem_centralizer_singleton_iff.mpr rfl)
  have hNxH : conjBy N e₀ ≤ Hn E := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem he₀H' (hNH hz)) (inv_mem he₀H')
  have hNY : N ≤ Hn E ⊓ centralizer ({r} : Set X) := le_inf hNH hNC
  have hNxY : conjBy N e₀ ≤ Hn E ⊓ centralizer ({r} : Set X) := le_inf hNxH hNxC
  have hNpc' := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hNY inf_le_right hNpc
  have hNxpc' := CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hNxY inf_le_right hNxpc
  have hAre : Ar.map (MulAut.conj e₀).toMonoidHom = Ar :=
    map_conj_eq_of_le_centralizer (hArle.trans inf_le_right)
  have hcc : (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom = N :=
    conjBy_conjBy_of_mul_self N he₀2
  by_cases h₁ : GSLit.fixedLayer M (zpowers r) = N
  · have hArN' : Ar ≤ N := h₁ ▸ hArMr
    have hArNx : Ar ≤ conjBy N e₀ := by
      rw [← hAre]
      exact map_mono hArN'
    exact false_of_le_coreActionKernel hArperf hArnt hArN' (hArNx.trans hNxK)
  by_cases h₂ : GSLit.fixedLayer M (zpowers r) = conjBy N e₀
  · have hArNx : Ar ≤ conjBy N e₀ := h₂ ▸ hArMr
    have hArN' : Ar ≤ N := by
      have h1 : Ar.map (MulAut.conj e₀).toMonoidHom ≤
          (conjBy N e₀).map (MulAut.conj e₀).toMonoidHom := map_mono hArNx
      rwa [hAre, hcc] at h1
    exact false_of_le_coreActionKernel hArperf hArnt hArNx (hArN'.trans hNKx)
  have hK1 : N ≤ UnbalancedLayer.coreActionKernel (GSLit.fixedLayer M (zpowers r)) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMrY hNY hMrpc hNpc' h₁
  have hK2 : conjBy N e₀ ≤ UnbalancedLayer.coreActionKernel (GSLit.fixedLayer M (zpowers r)) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMrY hNxY hMrpc hNxpc' h₂
  exact false_of_le_coreActionKernel hArperf hArnt hArMr (hcov.trans (sup_le hK1 hK2))

theorem pumpDiag_of_type (hs : Setting t J n e E D M) (hn : 11 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    (hOr : core (centralizer ({r} : Set X)) ≤ Hn E)
    (hFH : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (n - 4)))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    {N₁ : Subgroup X} (hN₁C : N₁ ≤ centralizer ({r} : Set X))
    (hN₁pc : IsPComponent 2 (N₁.subgroupOf (centralizer ({r} : Set X))))
    (hcov : fixA M e₀ r ≤ N₁ ⊔ conjBy N₁ e₀) {m : ℕ}
    (θ₁ : ↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m))
    (hcase : m = n - 4 ∨ (conjBy N₁ e₀ = N₁ ∧
      IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X)))))
    (hside : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r,
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N₁ ⊔ conjBy N₁ e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M) :
    conjBy N₁ e₀ = N₁ := by
  by_contra hdiag
  rcases hcase with h | ⟨h, -⟩
  · subst h
    exact false_of_diagonal hs hn hd he₀H hOr hFH χr hArle hArpc hN₁C hN₁pc hcov hdiag θ₁ hside
  · exact hdiag h

theorem pumpDiag_of_inputs (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) : PumpDiag := by
  intro X _ _ _ t J n e E D M hs hn e₀ F DF r hd he₀H hOr N₁ hP hside
  classical
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein hs.sig.klein).2 e₀ hd.e₀E
  have hFH := claimA_of_inputs h33 h35 hPump hN1 X t J n e E D M hs hn F hd.FJ hd.Fk DF hd.DFc
    hd.Fs
  obtain ⟨⟨χr⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  obtain ⟨N, hNC, hNpc, hAN, hNN₁, m, θN, -, -, hcase⟩ :=
    exists_typed_pump hPump hN1 hs hn hd χr hArle hArpc hP
  have hY : N ⊔ conjBy N e₀ = N₁ ⊔ conjBy N₁ e₀ := by
    rcases hNN₁ with h | h
    · rw [h]
    · rw [h, conjBy_conjBy_of_mul_self N₁ he₀2, sup_comm]
  have hside' : ∀ f ∈ F, ∃ a ∈ fixA M e₀ r,
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N ⊔ conjBy N e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
    intro f hf
    obtain ⟨a, ha, h1, h2⟩ := hside f hf
    exact ⟨a, ha, by rw [hY]; exact h1, h2⟩
  have hfix := pumpDiag_of_type hs (by omega) hd he₀H hOr hFH χr hArle hArpc hNC hNpc hAN θN
    hcase hside'
  rcases hNN₁ with h | h
  · rw [← h]
    exact hfix
  · have h1 : conjBy (conjBy N₁ e₀) e₀ = conjBy N₁ e₀ := by rw [← h]; exact hfix
    rw [conjBy_conjBy_of_mul_self N₁ he₀2] at h1
    exact h1.symm

end SwapP2

end CFSG.ComponentClassification.SolMax
