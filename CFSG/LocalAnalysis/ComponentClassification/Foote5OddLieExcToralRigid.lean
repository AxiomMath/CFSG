module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcToral
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcFieldPart
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTools

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank

variable {τ : Tag} {K : Type} [Field K]

theorem conj_eq_of_mem_toralCentralizer_bruhat
    (a' : Fin τ.rank → Kˣ) {g : ModGL τ K} (hg : g ∈ toralCentralizer τ K a')
    {w : WeylGroup τ} {h u v : ModGL τ K} (hh : h ∈ torusGroup τ K) (hu : u ∈ posUnipotent τ K)
    (hv : v ∈ rootSpan τ K (inversionSet w))
    (hgf : g = h * u * canonicalRep (coxeterSystem τ) K w * v) :
    rootDiagUnit τ a' * u * (rootDiagUnit τ a')⁻¹ = u ∧
      rootDiagUnit τ a' * v * (rootDiagUnit τ a')⁻¹ = v := by
  obtain ⟨hfac, huniq, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors τ K a'
  obtain ⟨w', -, h', hh', u', hu', v', hv', hg'⟩ := hfac g hg
  obtain ⟨-, -, huu, hvv⟩ := huniq w w' h h' u u' v v' hh hh' hu
    (rootSpan_mono Set.inter_subset_right hu') hv (rootSpan_mono Set.inter_subset_right hv')
    (hgf.symm.trans hg')
  have hc : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ rootCharKernel a' → ∀ y ∈ rootSpan τ K S,
      rootDiagUnit τ a' * y * (rootDiagUnit τ a')⁻¹ = y := fun hS y hy => by
    have := Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_le_centralizer a' hS hy)
    rw [← this, mul_inv_cancel_right]
  exact ⟨hc Set.inter_subset_left u (huu ▸ hu'), hc Set.inter_subset_left v (hvv ▸ hv')⟩

theorem exists_unit_sq_ne_one [Finite K] (hK5 : 5 ≤ Nat.card K) : ∃ l : Kˣ, l ^ 2 ≠ 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hlt : ({0, 1, -1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact lt_of_le_of_lt Finset.card_le_three (by omega)
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hz0, hz1, hz2⟩ := hz
  refine ⟨Units.mk0 z hz0, fun h => ?_⟩
  have h1 : z * z = 1 := by
    have := congrArg Units.val h
    simpa [sq] using this
  rcases mul_self_eq_one_iff.1 h1 with h2 | h2
  · exact hz1 h2
  · exact hz2 h2

theorem exists_rootDiagUnit_of_mem_toral
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) [Finite K] (hK2 : ringChar K ≠ 2)
    (hK5 : 5 ≤ Nat.card K) (hD : entryDegreeBound τ < ringChar K)
    (hcart : ∃ i k : Fin τ.rank, τ.cartan i k = -1)
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1) {i₀ : MulAut (adjointGroup τ K)}
    (hi₀ : ∀ h : adjointGroup τ K, (i₀ h : ModGL τ K) =
      rootDiagUnit τ c * h * (rootDiagUnit τ c)⁻¹)
    (hNF : ∀ r : MulAut (adjointGroup τ K), Odd (orderOf r) →
      ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (φ : K ≃+* K), ∀ h : adjointGroup τ K,
        (r h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
          Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
            (g : ModGL τ K)⁻¹)
    {R : Subgroup (MulAut (adjointGroup τ K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * i₀ = i₀ * r)
    (hRc : ∀ s : adjointGroup τ K, i₀ s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R)
    {r : MulAut (adjointGroup τ K)} (hr : r ∈ R) :
    ∃ e : Fin τ.rank → Kˣ, ∀ h : adjointGroup τ K,
      (r h : ModGL τ K) = rootDiagUnit τ e * h * (rootDiagUnit τ e)⁻¹ := by
  classical
  have hZ : center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have : Finite (ModGL τ K) := finite_modGL
  have hkerχ : rootCharKernel c = kernelRoots (maskChar (signTupleBits c)) :=
    rootCharKernel_eq_kernelRoots hK2 hc
  obtain ⟨-, -, -, hnorm, -, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K (maskChar (signTupleBits c))
  have hSX := rootSpan_rootCharKernel_le_toralCentralizer (K := K) (τ := τ) c
  have hXN := toralCentralizer_le_normalizer_rootSpan (K := K) (τ := τ) c
  have hfixX : ∀ s : adjointGroup τ K, i₀ s = s →
      (s : ModGL τ K) ∈ toralCentralizer τ K c := by
    intro s hs
    refine Subgroup.mem_inf.2 ⟨s.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := congrArg Subtype.val hs
    rw [hi₀] at h1
    calc (s : ModGL τ K) * rootDiagUnit τ c =
        (rootDiagUnit τ c * s * (rootDiagUnit τ c)⁻¹) * rootDiagUnit τ c := by rw [h1]
      _ = rootDiagUnit τ c * s := by group
  have hfixX' : ∀ s : adjointGroup τ K, (s : ModGL τ K) ∈ toralCentralizer τ K c → i₀ s = s := by
    intro s hs
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2
    rw [hi₀, ← h1, mul_inv_cancel_right]
  have hTfix : ∀ t ∈ oddFixed i₀, i₀ t = t := by
    have hle : oddFixed i₀ ≤ i₀.toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [oddFixed, closure_le]
      rintro s ⟨hs, -⟩
      exact hs
    exact fun t ht => hle ht
  have hfix : ∀ β ∈ rootCharKernel c, ∀ t : K,
      r ⟨pinnedX τ K β t, pinnedX_mem_adjointGroup β t⟩ =
        ⟨pinnedX τ K β t, pinnedX_mem_adjointGroup β t⟩ := by
    intro β hβ t
    have hβχ : β ∈ kernelRoots (maskChar (signTupleBits c)) := hkerχ ▸ hβ
    have hΨS : componentRootSpan K (maskChar (signTupleBits c)) ⟦⟨β, hβχ⟩⟧ ≤
        rootSpan τ K (rootCharKernel c) := by
      rw [hkerχ]
      exact (hnorm _).1
    have hΨn : ∀ a ∈ rootSpan τ K (rootCharKernel c),
        ∀ e ∈ componentRootSpan K (maskChar (signTupleBits c)) ⟦⟨β, hβχ⟩⟧,
          a * e * a⁻¹ ∈ componentRootSpan K (maskChar (signTupleBits c)) ⟦⟨β, hβχ⟩⟧ := by
      intro a ha e he
      have hN := (hnorm ⟦⟨β, hβχ⟩⟧).2
      have ha' : a ∈ rootSpan τ K (kernelRoots (maskChar (signTupleBits c))) := hkerχ ▸ ha
      exact (Subgroup.normal_subgroupOf_iff (hnorm _).1).1 hN e a he ha'
    have hEC : componentRootSpan K (maskChar (signTupleBits c)) ⟦⟨β, hβχ⟩⟧ ≤
        adjointGroup τ K := hΨS.trans (hSX.trans inf_le_left)
    have hq := componentRootSpan_quasisimple hK2 hK5 (maskChar (signTupleBits c)) ⟦⟨β, hβχ⟩⟧
    have hEq : CFSG.IsQuasisimple ((componentRootSpan K (maskChar (signTupleBits c))
        ⟦⟨β, hβχ⟩⟧).subgroupOf (adjointGroup τ K)) :=
      (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hEC)).2 hq
    have hcomp : GorensteinWalter.IsComponentOf ((componentRootSpan K
        (maskChar (signTupleBits c)) ⟦⟨β, hβχ⟩⟧).subgroupOf (adjointGroup τ K))
        (oddFixed i₀) := by
      refine ⟨(le_oddClosure_of_perfect le_rfl hEq.1.commutator_eq_top).trans
        (closure_mono ?_), ?_, gw_isQuasisimple_of_isQuasisimple hEq⟩
      · rintro g ⟨hgE, hgo⟩
        exact ⟨hfixX' g (hSX (hΨS hgE)), hgo⟩
      · refine isSubnormal_subgroupOf_of_conj
          (A := (rootSpan τ K (rootCharKernel c)).subgroupOf (adjointGroup τ K))
          (fun x hx => hΨS hx) (fun t ht a ha => ?_) (fun a ha _ e he => hΨn _ ha _ he)
        have htX := hfixX t (hTfix t ht)
        exact (Subgroup.mem_normalizer_iff.1 (hXN htX) (a : ModGL τ K)).1 ha
    exact fix_of_isComponentOf hRi hRc hZ hRodd hr hcomp
      (pinnedX_mem_rootSpan (S := {α | ∃ h : α ∈ kernelRoots (maskChar (signTupleBits c)),
        (⟦⟨α, h⟩⟧ : KernelComponent (maskChar (signTupleBits c))) = ⟦⟨β, hβχ⟩⟧})
        ⟨hβχ, rfl⟩ t)
  obtain ⟨g, a, φ, hgaφ⟩ := hNF r (odd_orderOf_of_mem hRodd hr)
  obtain ⟨x, hx⟩ : ∃ x : ModGL τ K, x = (g : ModGL τ K) * rootDiagUnit τ a := ⟨_, rfl⟩
  have hr' : ∀ h : adjointGroup τ K, (r h : ModGL τ K) =
      x * Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * x⁻¹ := fun h => by
    rw [hgaφ h, hx]
    group
  obtain ⟨β₀, hβ₀⟩ := exists_mem_rootCharKernel hc hcart
  have hφ1 : φ = 1 := by
    refine eq_one_of_conj_pinnedX hD (y := x) β₀ fun t => ?_
    have h1 := congrArg Subtype.val (hfix β₀ hβ₀ t)
    have h2 := hr' ⟨pinnedX τ K β₀ t, pinnedX_mem_adjointGroup β₀ t⟩
    rw [h1] at h2
    change pinnedX τ K β₀ t =
      x * Units.map (entrywiseHom φ.toRingHom) (pinnedX τ K β₀ t) * x⁻¹ at h2
    have hφX : Units.map (entrywiseHom φ.toRingHom) (pinnedX τ K β₀ t) = pinnedX τ K β₀ (φ t) :=
      Units.ext (entrywise_pinnedX φ.toRingHom β₀ t)
    rw [hφX] at h2
    exact h2.symm
  subst hφ1
  have hid : ∀ y : ModGL τ K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) y = y :=
    fun y => Units.ext (entrywise_id _)
  have hr1 : ∀ h : adjointGroup τ K, (r h : ModGL τ K) = x * h * x⁻¹ := fun h => by
    rw [hr', hid]
  have hxX : ∀ β ∈ rootCharKernel c, ∀ t : K,
      x * pinnedX τ K β t = pinnedX τ K β t * x := by
    intro β hβ t
    have h1 := congrArg Subtype.val (hfix β hβ t)
    rw [hr1] at h1
    change x * pinnedX τ K β t * x⁻¹ = pinnedX τ K β t at h1
    calc x * pinnedX τ K β t = (x * pinnedX τ K β t * x⁻¹) * x := by group
      _ = pinnedX τ K β t * x := by rw [h1]
  have hcomm_ac : rootDiagUnit τ a * rootDiagUnit τ c = rootDiagUnit τ c * rootDiagUnit τ a := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  obtain ⟨m, hmdef⟩ : ∃ m : ModGL τ K, m = x⁻¹ * (rootDiagUnit τ c)⁻¹ * x * rootDiagUnit τ c :=
    ⟨_, rfl⟩
  have hm : ∀ h : adjointGroup τ K, m * h * m⁻¹ = h := by
    intro h
    have e1 := congrArg (fun φ : MulAut (adjointGroup τ K) =>
      ((φ h : adjointGroup τ K) : ModGL τ K)) (hRi r hr)
    simp only [MulAut.mul_apply] at e1
    rw [hr1, hi₀, hi₀, hr1] at e1
    rw [hmdef]
    calc x⁻¹ * (rootDiagUnit τ c)⁻¹ * x * rootDiagUnit τ c * (h : ModGL τ K) *
          (x⁻¹ * (rootDiagUnit τ c)⁻¹ * x * rootDiagUnit τ c)⁻¹ =
        x⁻¹ * (rootDiagUnit τ c)⁻¹ * (x * (rootDiagUnit τ c * h * (rootDiagUnit τ c)⁻¹) * x⁻¹) *
          rootDiagUnit τ c * x := by group
      _ = x⁻¹ * (rootDiagUnit τ c)⁻¹ * (rootDiagUnit τ c * (x * h * x⁻¹) *
          (rootDiagUnit τ c)⁻¹) * rootDiagUnit τ c * x := by rw [e1]
      _ = h := by group
  have hmC : m ∈ adjointGroup τ K := by
    have hn : (g : ModGL τ K)⁻¹ * ((rootDiagUnit τ c)⁻¹ * g * rootDiagUnit τ c) ∈
        adjointGroup τ K := by
      refine mul_mem (inv_mem g.2) ?_
      have := conj_rootDiagUnit_mem_adjointGroup c⁻¹ g.2
      rwa [← rootDiagUnit_inv, inv_inv] at this
    have e : m = (rootDiagUnit τ a)⁻¹ *
        ((g : ModGL τ K)⁻¹ * ((rootDiagUnit τ c)⁻¹ * g * rootDiagUnit τ c)) *
          ((rootDiagUnit τ a)⁻¹)⁻¹ := by
      rw [hmdef, hx, inv_inv]
      simp only [mul_inv_rev, mul_assoc]
      rw [hcomm_ac]
    rw [e]
    have := conj_rootDiagUnit_mem_adjointGroup a⁻¹ hn
    rwa [← rootDiagUnit_inv] at this
  have hm1 : m = 1 := by
    have hz : (⟨m, hmC⟩ : adjointGroup τ K) ∈ center (adjointGroup τ K) := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      change (h : ModGL τ K) * m = m * h
      calc (h : ModGL τ K) * m = (m * h * m⁻¹) * m := by rw [hm h]
        _ = m * h := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hgc : (g : ModGL τ K) * rootDiagUnit τ c = rootDiagUnit τ c * g := by
    have hxc : x * rootDiagUnit τ c = rootDiagUnit τ c * x := by
      calc x * rootDiagUnit τ c = rootDiagUnit τ c * x * m := by rw [hmdef]; group
        _ = rootDiagUnit τ c * x := by rw [hm1, mul_one]
    rw [hx] at hxc
    have h1 : (g : ModGL τ K) * rootDiagUnit τ c * rootDiagUnit τ a =
        rootDiagUnit τ c * g * rootDiagUnit τ a := by
      calc (g : ModGL τ K) * rootDiagUnit τ c * rootDiagUnit τ a =
          (g : ModGL τ K) * (rootDiagUnit τ a * rootDiagUnit τ c) := by
            rw [mul_assoc, hcomm_ac]
        _ = rootDiagUnit τ c * (g * rootDiagUnit τ a) := by rw [← mul_assoc, hxc]
        _ = rootDiagUnit τ c * g * rootDiagUnit τ a := by group
    exact mul_right_cancel h1
  have hgX : (g : ModGL τ K) ∈ toralCentralizer τ K c :=
    Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 hgc⟩
  obtain ⟨l, hl⟩ := exists_unit_sq_ne_one hK5
  have hT : ∀ β : Fin τ.rank → ℤ, ∃ a' : Fin τ.rank → Kˣ, IsRoot τ β →
      rootTorusSL2 τ K β l = rootDiagUnit τ a' ∧ rootChar a' β = l ^ 2 := by
    intro β
    by_cases hβ : IsRoot τ β
    · obtain ⟨a', h1, h2⟩ := exists_rootTorusSL2_eq_rootDiagUnit (K := K) hβ l
      exact ⟨a', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hβ⟩
  choose A hA using hT
  have hgT : ∀ β ∈ rootCharKernel c, (g : ModGL τ K) ∈ toralCentralizer τ K (A β) := by
    intro β hβ
    have h1 := commute_rootSL2_of_commute hβ.1 (hxX β hβ) (hxX (-β) (neg_mem_rootCharKernel hβ))
      (HSL l)
    change x * rootTorusSL2 τ K β l = rootTorusSL2 τ K β l * x at h1
    rw [(hA β hβ.1).1, hx] at h1
    have hcomm' : rootDiagUnit τ a * rootDiagUnit τ (A β) =
        rootDiagUnit τ (A β) * rootDiagUnit τ a := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    refine Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h2 : (g : ModGL τ K) * rootDiagUnit τ (A β) * rootDiagUnit τ a =
        rootDiagUnit τ (A β) * g * rootDiagUnit τ a := by
      calc (g : ModGL τ K) * rootDiagUnit τ (A β) * rootDiagUnit τ a =
          (g : ModGL τ K) * (rootDiagUnit τ a * rootDiagUnit τ (A β)) := by
            rw [mul_assoc, hcomm']
        _ = rootDiagUnit τ (A β) * (g * rootDiagUnit τ a) := by rw [← mul_assoc, h1]
        _ = rootDiagUnit τ (A β) * g * rootDiagUnit τ a := by group
    exact mul_right_cancel h2
  obtain ⟨hfac, -, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors τ K c
  obtain ⟨w, hwc, h₀, hh₀, u, hu, v, hv, hgf⟩ := hfac g hgX
  have hu' : u ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu
  have hv' : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hparts := fun β (hβ : β ∈ rootCharKernel c) =>
    conj_eq_of_mem_toralCentralizer_bruhat (A β) (hgT β hβ) hh₀ hu' hv' hgf
  have hu1 : u = 1 := eq_one_of_conj_rootDiagUnit_eq
    (S := rootCharKernel c ∩ {α | IsRoot τ α ∧ 0 < height α}) (fun α hα => hα.2)
    (closedRoots_inter closedRoots_pos) hu A (fun β hβ => (hparts β hβ.1).1)
    (fun β hβ => by rw [(hA β hβ.1.1).2]; exact hl)
  have hv1 : v = 1 := eq_one_of_conj_rootDiagUnit_eq
    (S := rootCharKernel c ∩ inversionSet w) (fun α hα => inversionSet_pos hα.2)
    (closedRoots_inter (closedRoots_inversionSet w)) hv A (fun β hβ => (hparts β hβ.1).2)
    (fun β hβ => by rw [(hA β hβ.1.1).2]; exact hl)
  rw [hu1, hv1, mul_one, mul_one] at hgf
  have hwfix : ∀ β ∈ posRoots (rootCharKernel c), w • β = β := by
    intro β hβ
    have hβr : IsRoot τ β := hβ.1.1
    have h1 : x * pinnedX τ K β 1 * x⁻¹ = pinnedX τ K β 1 := by
      rw [hxX β hβ.1 1, mul_inv_cancel_right]
    have h2 : x * pinnedX τ K β 1 * x⁻¹ ∈ rootSubgroup τ K (w • β) := by
      rw [hx, hgf]
      have e : h₀ * canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ a * pinnedX τ K β 1 *
          (h₀ * canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ a)⁻¹ =
          h₀ * (canonicalRep (coxeterSystem τ) K w * (rootDiagUnit τ a * pinnedX τ K β 1 *
            (rootDiagUnit τ a)⁻¹) * (canonicalRep (coxeterSystem τ) K w)⁻¹) * h₀⁻¹ := by group
      rw [e, rootDiagUnit_conj_pinnedX a hβr]
      have h3 : canonicalRep (coxeterSystem τ) K w * pinnedX τ K β ((rootChar a β : K) * 1) *
          (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ rootSubgroup τ K (w • β) := by
        rw [← (canonical_weyl_root_transport τ K).2.1 w β hβr]
        exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨_, rfl⟩)
      exact (Subgroup.mem_normalizer_iff.1
        (torusGroup_le_normalizer_rootSubgroup (IsRoot.smul hβr w) hh₀) _).1 h3
    rw [h1] at h2
    obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 h2
    exact eq_of_pinnedX_eq_pinnedX_of_pos' (IsRoot.smul hβr w) hβr hβ.2 one_ne_zero hc'
  have hwK : w ∈ kernelPosStabilizer (maskChar (signTupleBits c)) := by
    refine ⟨(mem_rootCharStabilizer_iff hK2 hc).1 hwc, ?_⟩
    rw [← hkerχ]
    calc (w • ·) '' posRoots (rootCharKernel c) = id '' posRoots (rootCharKernel c) :=
          Set.image_congr fun β hβ => hwfix β hβ
      _ = posRoots (rootCharKernel c) := Set.image_id _
  obtain ⟨-, -, -, -, -, -, hcard1, -, -⟩ :=
    sign_kernel_positive_Weyl_component_representatives τ (maskChar (signTupleBits c))
  have hw1 : w = 1 := by
    have hsub : Subsingleton (kernelPosStabilizer (maskChar (signTupleBits c))) :=
      (Nat.card_eq_one_iff_unique.1 (hcard1 hτ)).1
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨w, hwK⟩ : kernelPosStabilizer (maskChar (signTupleBits c))) 1)
  rw [hw1, canonicalRep_one, mul_one] at hgf
  obtain ⟨l₀, hl₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh₀
  refine ⟨l₀ * a, fun h => ?_⟩
  rw [hr1, hx, hgf, hl₀, ← rootDiagUnit_mul]

theorem outerCoreAt_toral
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) [Finite K] (hK2 : ringChar K ≠ 2)
    (hK5 : 5 ≤ Nat.card K) (hD : entryDegreeBound τ < ringChar K)
    (hcart : ∃ i k : Fin τ.rank, τ.cartan i k = -1)
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1) {i₀ : MulAut (adjointGroup τ K)}
    (hi₀ : ∀ h : adjointGroup τ K, (i₀ h : ModGL τ K) =
      rootDiagUnit τ c * h * (rootDiagUnit τ c)⁻¹)
    (hNF : ∀ r : MulAut (adjointGroup τ K), Odd (orderOf r) →
      ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (φ : K ≃+* K), ∀ h : adjointGroup τ K,
        (r h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
          Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
            (g : ModGL τ K)⁻¹) :
    OuterCoreAt i₀ := by
  intro R hRodd hRi hRc r₁ h₁ r₂ h₂
  obtain ⟨e₁, he₁⟩ :=
    exists_rootDiagUnit_of_mem_toral hτ hK2 hK5 hD hcart hc hi₀ hNF hRodd hRi hRc h₁
  obtain ⟨e₂, he₂⟩ :=
    exists_rootDiagUnit_of_mem_toral hτ hK2 hK5 hD hcart hc hi₀ hNF hRodd hRi hRc h₂
  have h12 : rootDiagUnit τ e₁ * rootDiagUnit τ e₂ = rootDiagUnit τ e₂ * rootDiagUnit τ e₁ := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, he₁, he₂, he₂, he₁]
  calc rootDiagUnit τ e₁ * (rootDiagUnit τ e₂ * h * (rootDiagUnit τ e₂)⁻¹) *
        (rootDiagUnit τ e₁)⁻¹ =
      (rootDiagUnit τ e₁ * rootDiagUnit τ e₂) * h *
        (rootDiagUnit τ e₁ * rootDiagUnit τ e₂)⁻¹ := by group
    _ = (rootDiagUnit τ e₂ * rootDiagUnit τ e₁) * h *
        (rootDiagUnit τ e₂ * rootDiagUnit τ e₁)⁻¹ := by rw [h12]
    _ = rootDiagUnit τ e₂ * (rootDiagUnit τ e₁ * h * (rootDiagUnit τ e₁)⁻¹) *
        (rootDiagUnit τ e₂)⁻¹ := by group

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
