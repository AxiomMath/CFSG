module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabLemmas
public import CFSG.GH74.GLS.C3.Layer2.FinModelFacts

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2
open scoped Classical

theorem Tab.eT_symm_iT
    {n : ℕ} [NeZero n] (t : Tab n) (hn : n = 6 ∨ n = 7) (hv : t.Valid)
    (k : Fin 64) : (t.eT hn hv).symm (t.iT hn hv k) = k := by
  have := (t.eT hn hv).symm_apply_apply k
  rwa [eT_apply] at this

theorem fin_main_data
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (t : Tab n) (hv : t.Valid)
    (hc : t.claimB = true)
    (hF : ∃ a₀ : alternatingGroup (Fin (n + 4)), (a₀ : Perm (Fin (n + 4))) = a0perm n ∧
      ModelFacts n (embT n).range a₀ (embT n (x0T n)))
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ x, α (α x) = u * x * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (x : T0 n) (hx : (x : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(x : Amb n), hx⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α x : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V) :
    ∃ (φ : T0 n →* alternatingGroup (Fin (n + 4))) (a₀ : alternatingGroup (Fin (n + 4)))
      (s : T0 n),
    Function.Injective φ ∧ s * α s * u = 1 ∧ a₀ ^ 2 = 1 ∧ a₀ ∉ φ.range ∧
    (∀ t : T0 n, a₀ * φ t * a₀⁻¹ = φ (s * α t * s⁻¹)) ∧
    (∀ t : T0 n, orderOf t = 2 →
      (t ∈ X ∨ t ∈ V) ∧
        (t ∈ X ↔ numMoved ((φ t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4) ∧
        (t ∈ V ↔ numMoved ((φ t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 8)) ∧
    (∀ t : T0 n, orderOf (φ t * a₀) = 2 →
      numMoved (((φ t * a₀ : alternatingGroup (Fin (n + 4)))) : Perm (Fin (n + 4))) = 8) ∧
    (∀ η : ↥(Subgroup.centralizer {a₀} ⊓ (φ.range ⊔ Subgroup.zpowers a₀)) →*
        alternatingGroup (Fin (n + 4)),
      Function.Injective η →
      (∀ h : a₀ ∈ Subgroup.centralizer {a₀} ⊓ (φ.range ⊔ Subgroup.zpowers a₀),
        η ⟨a₀, h⟩ = φ (x0T n)) →
      (∀ w, η w ∈ φ.range) →
      ∃ w : ↥(Subgroup.centralizer {a₀} ⊓ (φ.range ⊔ Subgroup.zpowers a₀)), orderOf w = 2 ∧
        numMoved ((η w : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) ≠
          (if (w : alternatingGroup (Fin (n + 4))) ∈ φ.range then
            numMoved ((w : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) else 4)) ∧
    (∀ w ∈ φ.range ⊔ Subgroup.zpowers a₀, w ∉ φ.range → orderOf w = 2 →
      ∃ t : T0 n, φ t * a₀ * (φ t)⁻¹ = w) ∧
    (∀ y ∈ φ.range ⊔ Subgroup.zpowers a₀, orderOf y = 2 →
      Nat.card ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ Subgroup.zpowers a₀)) = 64 →
      y = φ (x0T n) ∨ y = a₀ * φ (x0T n) * a₀⁻¹) := by
  obtain ⟨a₀, ha₀, facts⟩ := hF
  set a : Tbl := t.tabOf hn hv α with ha_def
  have haut : t.IsAutT a := t.tabOf_isAut hn hv α
  have ha_spec : ∀ i, t.iT hn hv (a.get i) = α (t.iT hn hv i) := t.iT_tabOf hn hv α
  have hfun : (fun k : Fin 4 => a.get (t.gens.get k)) =
      ![a.get (t.gens.get 0), a.get (t.gens.get 1), a.get (t.gens.get 2),
        a.get (t.gens.get 3)] := by
    funext k
    fin_cases k <;> rfl
  have hgen : t.ofImages ![a.get (t.gens.get 0), a.get (t.gens.get 1), a.get (t.gens.get 2),
      a.get (t.gens.get 3)] = a := by
    rw [← hfun]
    exact (haut.eq_ofImages hv).symm
  have o0 : t.ok0 (a.get (t.gens.get 0)) = true := by
    simp only [Tab.ok0, beq_iff_eq]
    exact haut.cls3_eq _
  have o1 : t.ok1 (a.get (t.gens.get 0)) (a.get (t.gens.get 1)) = true := by
    simp only [Tab.ok1, Bool.and_eq_true, beq_iff_eq]
    exact ⟨haut.cls3_eq _, haut.pairOK _ _⟩
  have o2 : t.ok2 (a.get (t.gens.get 0)) (a.get (t.gens.get 1)) (a.get (t.gens.get 2)) = true := by
    simp only [Tab.ok2, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨haut.cls3_eq _, haut.pairOK _ _⟩, haut.pairOK _ _⟩
  have o3 : t.ok3 (a.get (t.gens.get 0)) (a.get (t.gens.get 1)) (a.get (t.gens.get 2))
      (a.get (t.gens.get 3)) = true := by
    simp only [Tab.ok3, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨haut.cls3_eq _, haut.pairOK _ _⟩, haut.pairOK _ _⟩, haut.pairOK _ _⟩
  have hfin : t.finalB t.autsOf a = true := by
    have := Tab.claim_apply t hc o0 o1 o2 o3 (by rw [hgen]; exact (Tab.isAutB_iff t a).2 haut)
    rwa [hgen] at this
  have hx' : a.get t.x0i ≠ t.x0i := by
    intro h
    apply hx
    have := congrArg (t.iT hn hv) h
    rw [ha_spec, Tab.iT_x0] at this
    exact this
  set ui : Fin 64 := (t.eT hn hv).symm u with hui
  have hiTui : t.iT hn hv ui = u := (t.eT hn hv).apply_symm_apply u
  have hu' : a.get ui = ui := by
    apply t.iT_injective hn hv
    rw [ha_spec, hiTui, hu]
  have hsq' : ∀ i, a.get (a.get i) = t.mulT (t.mulT ui i) (t.inv.get ui) := by
    intro i
    apply t.iT_injective hn hv
    rw [ha_spec, ha_spec, hsq, Tab.iT_mul, Tab.iT_mul, Tab.iT_inv, hiTui]
  have hclX' := Tab.edge_closed t hn hv α X hclX
  have hclV' := Tab.edge_closed t hn hv α V hclV
  have hX0 := Tab.reach_sound t hn hv a X hclX' t.x0i (by rw [Tab.iT_x0]; exact hX)
  have hV0 := Tab.reach_sound t hn hv a V hclV' (t.mulT t.x0i (a.get t.x0i))
    (by rw [Tab.iT_mul, ha_spec, Tab.iT_x0]; exact hV)
  have hdisj' : ∀ i, (t.reach a t.x0i).get i = true →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = true → False := by
    intro i h1 h2
    exact Set.disjoint_left.1 hdisj (hX0 i h1) (hV0 i h2)
  have hQ' : ∀ i, t.isQ.get i = true → i ≠ t.one →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = false := by
    intro i hi hi1
    by_contra hne
    have hV' : t.iT hn hv i ∈ V := hV0 i (by simpa using hne)
    refine hQ (t.iT hn hv i) ((hv.isQ_spec i).1 hi) ?_ hV'
    intro h
    apply hi1
    apply t.iT_injective hn hv
    rw [Tab.iT_one]
    exact h
  have hW := Tab.wB_of_ext t hn hv α hext
  obtain ⟨hcov, s, hs, ψ, hψL, hcert⟩ := Tab.final_unpack t hfin hx' ui hu' hsq' hdisj' hQ' hW
  have hψaut : t.IsAutT ψ := (Tab.isAutB_iff t ψ).1 (Tab.isAutB_of_mem_autsOf t hψL)
  obtain ⟨hψx0, hψconj, hψcol⟩ := Tab.certB_spec t hcert
  let ψT : T0 n →* T0 n :=
    { toFun := fun x => t.iT hn hv (ψ.get ((t.eT hn hv).symm x))
      map_one' := by
        have h1 : (t.eT hn hv).symm 1 = t.one := by
          apply (t.eT hn hv).injective
          rw [Equiv.apply_symm_apply, Tab.eT_apply, Tab.iT_one]
        show t.iT hn hv (ψ.get ((t.eT hn hv).symm 1)) = 1
        rw [h1, hψaut.one, Tab.iT_one]
      map_mul' := by
        intro x y
        obtain ⟨i, rfl⟩ := t.iT_surjective hn hv x
        obtain ⟨j, rfl⟩ := t.iT_surjective hn hv y
        show t.iT hn hv (ψ.get ((t.eT hn hv).symm (t.iT hn hv i * t.iT hn hv j))) = _
        rw [← Tab.iT_mul, Tab.eT_symm_iT, hψaut.hom, Tab.iT_mul, Tab.eT_symm_iT,
          Tab.eT_symm_iT] }
  have hψT_iT : ∀ i, ψT (t.iT hn hv i) = t.iT hn hv (ψ.get i) := by
    intro i
    show t.iT hn hv (ψ.get ((t.eT hn hv).symm (t.iT hn hv i))) = _
    rw [Tab.eT_symm_iT]
  have hψT_inj : Function.Injective ψT := by
    intro x y hxy
    obtain ⟨i, rfl⟩ := t.iT_surjective hn hv x
    obtain ⟨j, rfl⟩ := t.iT_surjective hn hv y
    rw [hψT_iT, hψT_iT] at hxy
    have := hψaut.inj _ _ (t.iT_injective hn hv hxy)
    rw [this]
  have hψT_surj : Function.Surjective ψT := Finite.injective_iff_surjective.1 hψT_inj
  let φ : T0 n →* alternatingGroup (Fin (n + 4)) := (embT n).comp ψT
  have hφ_apply : ∀ x, φ x = embT n (ψT x) := fun x => rfl
  have hφR : φ.range = (embT n).range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ψT x, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y', hy'⟩ := hψT_surj x
      exact ⟨y', by rw [hφ_apply, hy']⟩
  have hφx0 : φ (x0T n) = embT n (x0T n) := by
    rw [hφ_apply, ← Tab.iT_x0 t hn hv, hψT_iT, hψx0]
  have facts' : ModelFacts n φ.range a₀ (φ (x0T n)) := by
    rw [hφR, hφx0]
    exact facts
  set sT : T0 n := t.iT hn hv s with hsT
  have hs' : sT * α sT * u = 1 := by
    have := congrArg (t.iT hn hv) hs
    rwa [Tab.iT_mul, Tab.iT_mul, ha_spec, hiTui, Tab.iT_one] at this
  have hφnm : ∀ x : T0 n, numMoved ((φ x : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) =
      t.nm.get (ψ.get ((t.eT hn hv).symm x)) := by
    intro x
    rw [hv.nm_spec]
    rfl
  refine ⟨φ, a₀, sT, (embT_injective n).comp hψT_inj, hs', facts'.sq, facts'.notin, ?_, ?_, ?_,
    ?_, ?_, facts'.cent⟩
  ·
    intro x
    obtain ⟨i, rfl⟩ := t.iT_surjective hn hv x
    apply Subtype.ext
    have e1 : ((a₀ * φ (t.iT hn hv i) * a₀⁻¹ : alternatingGroup (Fin (n + 4))) :
        Perm (Fin (n + 4))) =
        a0perm n * emb n (t.el.get (ψ.get i)) * (a0perm n)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha₀, hφ_apply, hψT_iT]
      rfl
    have e2 : sT * α (t.iT hn hv i) * sT⁻¹ =
        t.iT hn hv (t.mulT (t.mulT s (a.get i)) (t.inv.get s)) := by
      rw [Tab.iT_mul, Tab.iT_mul, ha_spec, Tab.iT_inv]
    have e3 : ((φ (sT * α (t.iT hn hv i) * sT⁻¹) : alternatingGroup (Fin (n + 4))) :
        Perm (Fin (n + 4))) = emb n (t.el.get (t.astar.get (ψ.get i))) := by
      rw [e2, hφ_apply, hψT_iT, hψconj i]
      rfl
    rw [e1, e3, hv.astar_spec]
  ·
    intro x hx2
    set i := (t.eT hn hv).symm x with hi
    have hix : t.iT hn hv i = x := (t.eT hn hv).apply_symm_apply x
    have hinvB : t.isInv i = true := Tab.isInv_of_orderOf t hn hv hx2
    have hnm := hφnm x
    obtain ⟨hc4X, hc4V⟩ := hψcol i hinvB
    have hxX : (t.reach a t.x0i).get i = true → x ∈ X := fun h => hix ▸ hX0 i h
    have hxV : (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = true → x ∈ V :=
      fun h => hix ▸ hV0 i h
    refine ⟨?_, ?_, ?_⟩
    · rcases hcov i hinvB with h | h
      · exact Or.inl (hxX h)
      · exact Or.inr (hxV h)
    · constructor
      · intro hxX'
        rcases hcov i hinvB with h | h
        · rw [hnm]; exact hc4X h
        · exact absurd (hxV h) (fun hv' => Set.disjoint_left.1 hdisj hxX' hv')
      · intro h4
        rcases hcov i hinvB with h | h
        · exact hxX h
        · have h8 := hc4V h
          rw [hnm] at h4
          exact absurd (h8.symm.trans h4) (by decide)
    · constructor
      · intro hxV'
        rcases hcov i hinvB with h | h
        · exact absurd hxV' (fun hv' => Set.disjoint_left.1 hdisj (hxX h) hv')
        · rw [hnm]; exact hc4V h
      · intro h8
        rcases hcov i hinvB with h | h
        · have h4 := hc4X h
          rw [hnm] at h8
          exact absurd (h4.symm.trans h8) (by decide)
        · exact hxV h
  ·
    intro x hx2
    exact facts'.odd (φ x) ⟨x, rfl⟩ hx2
  ·
    intro η hη h0 hR
    obtain ⟨w, hw2, hne⟩ := facts'.eta η hη h0 hR
    refine ⟨w, hw2, ?_⟩
    by_cases hmem : (w : alternatingGroup (Fin (n + 4))) ∈ φ.range
    · simp only [hmem, ite_true] at hne ⊢
      exact hne
    · simp only [hmem, ite_false] at hne ⊢
      exact hne
  ·
    intro w hw hwn hw2
    obtain ⟨r, ⟨x, rfl⟩, hr⟩ := facts'.conj w hw hwn hw2
    exact ⟨x, hr⟩

end CFSG.GH74.GLS.C3.Layer2.Model
