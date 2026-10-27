module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.BookkeepingCocycle
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Twist

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {V : Type} [CommGroup V]

theorem commV_mono {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : commV X ≤ commV Y :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ => ⟨x, h hx, v, hv⟩

theorem mul_inv_mem_commV {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) (v : V) :
    x v * v⁻¹ ∈ commV X :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem apply_mem_commV_of_conj {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {w : V} (hw : w ∈ commV X) : g w ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hg hw

theorem apply_mem_fixV_of_conj {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {w : V} (hw : w ∈ fixV X) : g w ∈ fixV X := by
  intro x hx
  have h1 := congrArg g (hw _ (hg x hx))
  simpa [MulAut.mul_apply, MulAut.apply_inv_self] using h1

theorem mem_fixV_of_perfect {G : Type*} [Group G] (hG : commutator G = ⊤)
    {L : Subgroup (MulAut V)} (ρ : G →* ↥L) (hρ : Function.Surjective ρ) {w : V}
    (hw : ∀ l ∈ L, l w * w⁻¹ ∈ fixV L) : w ∈ fixV L := by
  let φ : G →* ↥(fixV L) :=
    { toFun := fun g => ⟨(ρ g : MulAut V) w * w⁻¹, hw _ (ρ g).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (ρ (a * b) : MulAut V) w * w⁻¹ =
          ((ρ a : MulAut V) w * w⁻¹) * ((ρ b : MulAut V) w * w⁻¹)
        rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
        have hc : (ρ a : MulAut V) ((ρ b : MulAut V) w * w⁻¹) = (ρ b : MulAut V) w * w⁻¹ :=
          hw _ (ρ b).2 _ (ρ a).2
        rw [map_mul, map_inv] at hc
        calc (ρ a : MulAut V) ((ρ b : MulAut V) w) * w⁻¹
            = ((ρ a : MulAut V) ((ρ b : MulAut V) w) * ((ρ a : MulAut V) w)⁻¹) *
                ((ρ a : MulAut V) w * w⁻¹) := by group
          _ = _ := by rw [hc]; exact mul_comm _ _) }
  intro x hx
  obtain ⟨g, hg⟩ := hρ ⟨x, hx⟩
  have h1 : φ g = 1 := Abelianization.commutator_subset_ker φ (hG ▸ Subgroup.mem_top g)
  have h2 : (ρ g : MulAut V) w * w⁻¹ = 1 := congrArg Subtype.val h1
  rw [hg] at h2
  exact mul_inv_eq_one.1 h2

variable {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem apply_mem_commV_altPre (h : ↥H) {w : V} (hw : w ∈ commV (altPre ψ)) :
    (h : MulAut V) w ∈ commV (altPre ψ) :=
  apply_mem_commV_of_conj (fun _ hx => conj_mem_altPre h.2 hx) hw

theorem apply_mem_fixV_altPre (h : ↥H) {w : V} (hw : w ∈ fixV (altPre ψ)) :
    (h : MulAut V) w ∈ fixV (altPre ψ) :=
  apply_mem_fixV_of_conj (fun x hx => by
    have := conj_mem_altPre (H.inv_mem h.2) hx
    rwa [inv_inv] at this) hw

theorem natThrough_equivariant (hn : 5 ≤ n) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    {π : ↥(commV (altPre ψ)) →* Multiplicative (altHeart n)} (hπ : Function.Surjective π)
    (hker : π.ker = (commV (altPre ψ) ⊓ fixV (altPre ψ)).subgroupOf (commV (altPre ψ)))
    (heq : ∀ (l : ↥(altPre ψ)) (u v : ↥(commV (altPre ψ))), (v : V) = (l : MulAut V) (u : V) →
      Multiplicative.toAdd (π v) =
        altAct ((ψ.comp (Subgroup.inclusion altPre_le)) l) (Multiplicative.toAdd (π u)))
    (h : ↥H) (u v : ↥(commV (altPre ψ))) (huv : (v : V) = (h : MulAut V) (u : V)) :
    Multiplicative.toAdd (π v) = altAct (ψ h) (Multiplicative.toAdd (π u)) := by
  classical
  have hker' : ∀ a : ↥(commV (altPre ψ)), π a = 1 ↔ (a : V) ∈ fixV (altPre ψ) := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  let hU : ∀ g : ↥H, ↥(commV (altPre ψ)) → ↥(commV (altPre ψ)) := fun g a =>
    ⟨(g : MulAut V) a, apply_mem_commV_altPre g a.2⟩
  have hU_mul : ∀ (g : ↥H) (a b : ↥(commV (altPre ψ))), hU g (a * b) = hU g a * hU g b :=
    fun g a b => Subtype.ext (map_mul _ _ _)
  have hU_inv : ∀ (g : ↥H) (a : ↥(commV (altPre ψ))), hU g a⁻¹ = (hU g a)⁻¹ :=
    fun g a => Subtype.ext (map_inv _ _)
  have hresp : ∀ a b : ↥(commV (altPre ψ)), π a = π b → π (hU h a) = π (hU h b) := by
    intro a b hab
    have h1 : π (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 := apply_mem_fixV_altPre h ((hker' _).1 h1)
    have h3 : π (hU h a * (hU h b)⁻¹) = 1 := by
      rw [← hU_inv, ← hU_mul]
      exact (hker' _).2 h2
    rwa [map_mul, map_inv, mul_inv_eq_one] at h3
  choose s hs using fun y : altHeart n => hπ (Multiplicative.ofAdd y)
  let g : altHeart n →+ altHeart n :=
    { toFun := fun y => altAct (ψ h)⁻¹ (Multiplicative.toAdd (π (hU h (s y))))
      map_zero' := by
        have h1 : π (hU h (s 0)) = π (hU h 1) := hresp _ _ (by rw [hs, map_one]; rfl)
        have h2 : hU h 1 = 1 := Subtype.ext (map_one _)
        simp only [h1, h2, map_one, toAdd_one, map_zero]
      map_add' := fun y₁ y₂ => by
        have h1 : π (hU h (s (y₁ + y₂))) = π (hU h (s y₁ * s y₂)) :=
          hresp _ _ (by rw [hs, map_mul, hs, hs]; rfl)
        simp only [h1, hU_mul, map_mul, toAdd_mul, map_add] }
  have hg : ∀ a : ↥(commV (altPre ψ)),
      g (Multiplicative.toAdd (π a)) = altAct (ψ h)⁻¹ (Multiplicative.toAdd (π (hU h a))) := by
    intro a
    change altAct (ψ h)⁻¹ (Multiplicative.toAdd (π (hU h (s _)))) = _
    rw [hresp _ a (by rw [hs]; rfl)]
  have hcomm : ∀ σ ∈ alternatingGroup (Fin n), ∀ y, g (altAct σ y) = altAct σ (g y) := by
    intro σ hσ y
    obtain ⟨l, hl⟩ := altPreHom_surjective hA ⟨σ, hσ⟩
    have hlσ : ψ (Subgroup.inclusion altPre_le l) = σ := by
      rw [← coe_altPreHom, hl]
    obtain ⟨a, rfl⟩ : ∃ a : ↥(commV (altPre ψ)), Multiplicative.toAdd (π a) = y :=
      ⟨s y, by rw [hs]; rfl⟩
    let la : ↥(commV (altPre ψ)) := hU (Subgroup.inclusion altPre_le l) a
    have h1 : altAct σ (Multiplicative.toAdd (π a)) = Multiplicative.toAdd (π la) := by
      rw [heq l a la rfl, MonoidHom.comp_apply, hlσ]
    let l' : ↥(altPre ψ) := ⟨(h : MulAut V) * l * (h : MulAut V)⁻¹, conj_mem_altPre h.2 l.2⟩
    have h2 : Multiplicative.toAdd (π (hU h la)) =
        altAct (ψ (Subgroup.inclusion altPre_le l')) (Multiplicative.toAdd (π (hU h a))) := by
      refine heq l' (hU h a) (hU h la) ?_
      change (h : MulAut V) ((l : MulAut V) a) =
        ((h : MulAut V) * l * (h : MulAut V)⁻¹) ((h : MulAut V) a)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    have h3 : ψ (Subgroup.inclusion altPre_le l') = ψ h * σ * (ψ h)⁻¹ := by
      have : Subgroup.inclusion altPre_le l' = h * Subgroup.inclusion altPre_le l * h⁻¹ :=
        Subtype.ext rfl
      rw [this, map_mul, map_mul, map_inv, hlσ]
    rw [h1, hg, hg, h2, h3, ← altAct_mul, ← altAct_mul]
    congr 1
    group
  have := altHeart_nontrivial (n := n) (by omega)
  rcases altHeart_endo_eq_zero_or_id hn g hcomm with h0 | hid
  · exfalso
    have hall : ∀ a : ↥(commV (altPre ψ)), π a = 1 := by
      intro a
      let b : ↥(commV (altPre ψ)) := hU h⁻¹ a
      have hb : hU h b = a := Subtype.ext (by
        change (h : MulAut V) (((h⁻¹ : ↥H) : MulAut V) a) = a
        rw [Subgroup.coe_inv, MulAut.apply_inv_self])
      have h4 := hg b
      rw [h0, AddMonoidHom.zero_apply, hb] at h4
      have h5 := congrArg (altAct (ψ h)) h4
      rw [map_zero, altAct_apply_inv] at h5
      exact Multiplicative.toAdd.injective (h5.symm.trans toAdd_one.symm)
    obtain ⟨y, hy⟩ := exists_ne (0 : altHeart n)
    obtain ⟨a, ha⟩ := hπ (Multiplicative.ofAdd y)
    rw [hall a] at ha
    exact hy (congrArg Multiplicative.toAdd ha).symm
  · have h4 := hg u
    rw [hid, AddMonoidHom.id_apply] at h4
    have hv : v = hU h u := Subtype.ext huv
    rw [hv, h4, altAct_apply_inv]

theorem mem_sup_trichotomy (hn : 7 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hnat : NatThrough (altPre ψ) (ψ.comp (Subgroup.inclusion altPre_le)) (commV (altPre ψ)))
    (v v' : V) :
    v ∈ commV (altPre ψ) ⊔ fixV (altPre ψ) ∨ v' ∈ commV (altPre ψ) ⊔ fixV (altPre ψ) ∨
      v * v'⁻¹ ∈ commV (altPre ψ) ⊔ fixV (altPre ψ) := by
  classical
  obtain ⟨π, hπ, hker, heq⟩ := hnat
  have hker' : ∀ a : ↥(commV (altPre ψ)), π a = 1 ↔ (a : V) ∈ fixV (altPre ψ) := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  have hbij : Function.Bijective (altPreHom ψ) :=
    ⟨altPreHom_injective hψ, altPreHom_surjective hA⟩
  set e : alternatingGroup (Fin n) ≃* ↥(altPre ψ) := (MulEquiv.ofBijective _ hbij).symm with he
  have hψe : ∀ σ : alternatingGroup (Fin n), ψ (Subgroup.inclusion altPre_le (e σ)) = σ := by
    intro σ
    rw [← coe_altPreHom]
    exact congrArg Subtype.val ((MulEquiv.ofBijective _ hbij).apply_symm_apply σ)
  have he_alt : ∀ l : ↥(altPre ψ), e (altPreHom ψ l) = l := fun l =>
    (MulEquiv.ofBijective _ hbij).symm_apply_apply l
  let cv : V → Perm (Fin n) → altHeart n := fun w σ =>
    if hσ : σ ∈ alternatingGroup (Fin n) then
      Multiplicative.toAdd (π ⟨(e ⟨σ, hσ⟩ : MulAut V) w * w⁻¹, mul_inv_mem_commV (e _).2 w⟩)
    else 0
  have hcv : ∀ (w : V) (σ : Perm (Fin n)) (hσ : σ ∈ alternatingGroup (Fin n)),
      cv w σ = Multiplicative.toAdd
        (π ⟨(e ⟨σ, hσ⟩ : MulAut V) w * w⁻¹, mul_inv_mem_commV (e _).2 w⟩) :=
    fun w σ hσ => dite_eq_left hσ
  have hcoc : ∀ w : V, ∀ σ ∈ alternatingGroup (Fin n), ∀ τ ∈ alternatingGroup (Fin n),
      cv w (σ * τ) = cv w σ + altAct σ (cv w τ) := by
    intro w σ hσ τ hτ
    rw [hcv w _ (mul_mem hσ hτ), hcv w σ hσ, hcv w τ hτ]
    have he_mul : e ⟨σ * τ, mul_mem hσ hτ⟩ = e ⟨σ, hσ⟩ * e ⟨τ, hτ⟩ := by
      rw [← map_mul]; rfl
    have hmem : (e ⟨σ, hσ⟩ : MulAut V) ((e ⟨τ, hτ⟩ : MulAut V) w * w⁻¹) ∈ commV (altPre ψ) :=
      apply_mem_commV_altPre (Subgroup.inclusion altPre_le (e ⟨σ, hσ⟩))
        (mul_inv_mem_commV (e _).2 w)
    have hsplit : (⟨(e ⟨σ * τ, mul_mem hσ hτ⟩ : MulAut V) w * w⁻¹,
        mul_inv_mem_commV (e _).2 w⟩ : ↥(commV (altPre ψ))) =
        ⟨_, hmem⟩ * ⟨(e ⟨σ, hσ⟩ : MulAut V) w * w⁻¹, mul_inv_mem_commV (e _).2 w⟩ := by
      refine Subtype.ext ?_
      change (e ⟨σ * τ, mul_mem hσ hτ⟩ : MulAut V) w * w⁻¹ =
        (e ⟨σ, hσ⟩ : MulAut V) ((e ⟨τ, hτ⟩ : MulAut V) w * w⁻¹) *
          ((e ⟨σ, hσ⟩ : MulAut V) w * w⁻¹)
      rw [he_mul, Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
      group
    rw [hsplit, map_mul, toAdd_mul,
      heq (e ⟨σ, hσ⟩) ⟨(e ⟨τ, hτ⟩ : MulAut V) w * w⁻¹, mul_inv_mem_commV (e _).2 w⟩ ⟨_, hmem⟩ rfl,
      MonoidHom.comp_apply, hψe]
    exact add_comm _ _
  have hcv_div : ∀ (w w' : V) (σ : Perm (Fin n)), σ ∈ alternatingGroup (Fin n) →
      cv (w * w'⁻¹) σ = cv w σ - cv w' σ := by
    intro w w' σ hσ
    rw [hcv _ σ hσ, hcv w σ hσ, hcv w' σ hσ]
    have hsplit : (⟨(e ⟨σ, hσ⟩ : MulAut V) (w * w'⁻¹) * (w * w'⁻¹)⁻¹,
        mul_inv_mem_commV (e _).2 _⟩ : ↥(commV (altPre ψ))) =
        ⟨(e ⟨σ, hσ⟩ : MulAut V) w * w⁻¹, mul_inv_mem_commV (e _).2 w⟩ *
          (⟨(e ⟨σ, hσ⟩ : MulAut V) w' * w'⁻¹, mul_inv_mem_commV (e _).2 w'⟩)⁻¹ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_inv_rev, inv_inv]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [hsplit, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hcob : ∀ (w : V) (z : altHeart n), (∀ g ∈ alternatingGroup (Fin n),
      cv w g = altAct g z - z) → w ∈ commV (altPre ψ) ⊔ fixV (altPre ψ) := by
    intro w z hz
    obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd z)
    have h5 : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    have hfix : w * (u : V)⁻¹ ∈ fixV (altPre ψ) := by
      refine mem_fixV_of_perfect (commutator_alternatingGroup_eq_top h5) e.toMonoidHom
        e.surjective fun l hl => ?_
      set l₀ : ↥(altPre ψ) := ⟨l, hl⟩
      set σ := altPreHom ψ l₀ with hσ
      have hel : e ⟨(σ : Perm (Fin n)), σ.2⟩ = l₀ := he_alt l₀
      have hlu : l (u : V) ∈ commV (altPre ψ) :=
        apply_mem_commV_altPre (Subgroup.inclusion altPre_le l₀) u.2
      have h1 : Multiplicative.toAdd (π ⟨l w * w⁻¹, mul_inv_mem_commV hl w⟩) =
          altAct σ z - z := by
        rw [← hz σ σ.2, hcv w σ σ.2]
        exact congrArg (fun a => Multiplicative.toAdd (π a)) (Subtype.ext (by rw [hel]))
      have h2 : Multiplicative.toAdd (π ⟨l (u : V) * (u : V)⁻¹, mul_inv_mem_commV hl u⟩) =
          altAct σ z - z := by
        have hsplit : (⟨l (u : V) * (u : V)⁻¹, mul_inv_mem_commV hl u⟩ :
            ↥(commV (altPre ψ))) = ⟨l (u : V), hlu⟩ * u⁻¹ := Subtype.ext rfl
        rw [hsplit, map_mul, map_inv, toAdd_mul, toAdd_inv, heq l₀ u ⟨l (u : V), hlu⟩ rfl, hu,
          toAdd_ofAdd, MonoidHom.comp_apply, ← coe_altPreHom, ← sub_eq_add_neg]
      have h3 : π (⟨l w * w⁻¹, mul_inv_mem_commV hl w⟩ *
          (⟨l (u : V) * (u : V)⁻¹, mul_inv_mem_commV hl u⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, h1, h2, add_neg_cancel, toAdd_one]
      have h4 := (hker' _).1 h3
      have h5 : l (w * (u : V)⁻¹) * (w * (u : V)⁻¹)⁻¹ =
          (l w * w⁻¹) * (l (u : V) * (u : V)⁻¹)⁻¹ := by
        simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
        simp only [mul_comm, mul_left_comm, mul_assoc]
      rw [h5]
      exact h4
    have hw : w = (u : V) * (w * (u : V)⁻¹) := by rw [mul_comm w, mul_inv_cancel_left]
    rw [hw]
    exact Subgroup.mul_mem_sup u.2 hfix
  obtain ⟨k⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨z, hz | hz⟩ := altCocycle_cases hn k (cv v) (hcoc v)
  · exact Or.inl (hcob v z hz)
  obtain ⟨z', hz' | hz'⟩ := altCocycle_cases hn k (cv v') (hcoc v')
  · exact Or.inr (Or.inl (hcob v' z' hz'))
  refine Or.inr (Or.inr (hcob _ (z - z') fun g hg => ?_))
  rw [hcv_div v v' g hg, hz g hg, hz' g hg, map_sub]
  abel

theorem commV_le_sup_of_natThrough (hn : 7 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hnat : NatThrough (altPre ψ) (ψ.comp (Subgroup.inclusion altPre_le)) (commV (altPre ψ))) :
    commV H ≤ commV (altPre ψ) ⊔ fixV (altPre ψ) := by
  set M := commV (altPre ψ) ⊔ fixV (altPre ψ) with hM
  have hMinv : ∀ (g : ↥H) (w : V), w ∈ M → (g : MulAut V) w ∈ M := by
    intro g w hw
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul]
    exact Subgroup.mul_mem_sup (apply_mem_commV_altPre g ha) (apply_mem_fixV_altPre g hc)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  set g : ↥H := ⟨x, hx⟩
  rcases mem_sup_trichotomy hn hψ hA hnat v (x v) with h1 | h2 | h3
  · exact M.mul_mem (hMinv g v h1) (M.inv_mem h1)
  · have hv : v ∈ M := by
      have := hMinv g⁻¹ _ h2
      rwa [Subgroup.coe_inv, MulAut.inv_apply_self] at this
    exact M.mul_mem h2 (M.inv_mem hv)
  · have := M.inv_mem h3
    rwa [mul_inv_rev, inv_inv] at this

theorem natVia_commV_of_natThrough (hn : 7 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hnat : NatThrough (altPre ψ) (ψ.comp (Subgroup.inclusion altPre_le)) (commV (altPre ψ))) :
    NatVia ψ (commV H) := by
  classical
  have hle := commV_le_sup_of_natThrough hn hψ hA hnat
  obtain ⟨π, hπ, hker, heq⟩ := hnat
  have hker' : ∀ a : ↥(commV (altPre ψ)), π a = 1 ↔ (a : V) ∈ fixV (altPre ψ) := fun a => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  have hLH : commV (altPre ψ) ≤ commV H := commV_mono altPre_le
  have hdec : ∀ w : ↥(commV H), ∃ u : ↥(commV (altPre ψ)), ∃ c ∈ fixV (altPre ψ),
      (u : V) * c = w := fun w => by
    obtain ⟨u, hu, c, hc, huc⟩ := Subgroup.mem_sup.1 (hle w.2)
    exact ⟨⟨u, hu⟩, c, hc, huc⟩
  choose dU dC hdC hd using hdec
  have hwd : ∀ (u u' : ↥(commV (altPre ψ))) (c c' : V), c ∈ fixV (altPre ψ) →
      c' ∈ fixV (altPre ψ) → (u : V) * c = u' * c' → π u = π u' := by
    intro u u' c c' hc hc' huc
    have h1 : ((u * u'⁻¹ : ↥(commV (altPre ψ))) : V) = c' * c⁻¹ := by
      have h0 : (u : V) = u' * c' * c⁻¹ := by rw [← huc, mul_inv_cancel_right]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h0, mul_right_comm _ _ (u' : V)⁻¹,
        mul_right_comm (u' : V) c' (u' : V)⁻¹, mul_inv_cancel, one_mul]
    have h2 : π (u * u'⁻¹) = 1 := (hker' _).2 (h1 ▸ mul_mem hc' (inv_mem hc))
    rwa [map_mul, map_inv, mul_inv_eq_one] at h2
  let π' : ↥(commV H) →* Multiplicative (altHeart n) :=
    { toFun := fun w => π (dU w)
      map_one' := by
        rw [← map_one π]
        exact hwd _ 1 _ 1 (hdC 1) (one_mem _) (by rw [hd]; simp)
      map_mul' := fun w₁ w₂ => by
        rw [← map_mul]
        refine hwd _ _ (dC (w₁ * w₂)) (dC w₁ * dC w₂) (hdC _) (mul_mem (hdC w₁) (hdC w₂)) ?_
        rw [hd, Subgroup.coe_mul, Subgroup.coe_mul, mul_mul_mul_comm, hd, hd] }
  have hπ' : ∀ w, π' w = π (dU w) := fun _ => rfl
  refine ⟨π', fun y => ?_, ?_, fun h w w' hww' => ?_⟩
  · obtain ⟨u, hu⟩ := hπ y
    refine ⟨⟨u, hLH u.2⟩, ?_⟩
    rw [hπ', ← hu]
    exact hwd _ _ _ 1 (hdC _) (one_mem _) (by rw [hd, mul_one])
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hπ', hker']
    constructor
    · intro h1
      refine ⟨w.2, ?_⟩
      rw [← hd w]
      exact mul_mem h1 (hdC w)
    · rintro ⟨-, h1⟩
      have : (dU w : V) = w * (dC w)⁻¹ := by rw [← hd w, mul_inv_cancel_right]
      rw [this]
      exact mul_mem h1 (inv_mem (hdC w))
  ·
    have hhu : (h : MulAut V) (dU w) ∈ commV (altPre ψ) := apply_mem_commV_altPre h (dU w).2
    have h1 : π (dU w') = π ⟨(h : MulAut V) (dU w), hhu⟩ :=
      hwd _ _ _ _ (hdC w') (apply_mem_fixV_altPre h (hdC w)) (by
        rw [hd, hww', ← hd w, map_mul])
    rw [hπ', hπ', h1]
    exact natThrough_equivariant (by omega) hA hπ hker heq h (dU w) _ rfl

theorem natVia_commV_of_isAltNaturalSection (hn : 7 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h : IsAltNaturalSection (altPre ψ) (commV (altPre ψ)) n) :
    commV H ≤ commV (altPre ψ) ⊔ fixV (altPre ψ) ∧ NatVia ψ (commV H) := by
  have hnat := natThrough_of_isAltNaturalSection (by omega) (by omega) hψ hA h
  exact ⟨commV_le_sup_of_natThrough hn hψ hA hnat, natVia_commV_of_natThrough hn hψ hA hnat⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
