module

public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.CocycleGen
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Core
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Decomp
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.ModuleStepGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Open
  CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_small_support_decomposition {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {d : ℕ}
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (T Γ : Finset (Fin d)) (hfree : ∃ i, i ∉ T ∧ i ∉ Γ) (hTΓ : Disjoint T Γ)
    {g : G} (hgL : g ∈ L) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) (hg3 : g ^ 3 = 1)
    (hgT : ∀ x ∉ T, θ ⟨g, (le_sup_left : L ≤ L ⊔ S) hgL⟩ x = x)
    (hcN : θ ⟨g, (le_sup_left : L ≤ L ⊔ S) hgL⟩ ∉ Subgroup.normalizer
      ((((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin d))) :
        Set (Perm (Fin d))))
    (hdecomp : ∀ s ∈ S, ∃ j ∈ thompsonJ S, ∃ δ : ↥(L ⊔ S), (δ : G) ∈ S ∧
      (∀ x ∉ Γ, θ δ x = x) ∧ s = (δ : G) * j)
    (hZC : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ v ∈ blockV S L, z * v = v * z)
    (hZL : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ l ∈ L, ⁅l, z⁆ ∈ blockV S L)
    (hXL : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ k : ↥(L ⊔ S), θ k = 1 → ∀ l ∈ L,
      l * ⁅(k : G), z⁆ = ⁅(k : G), z⁆ * l)
    (hne : ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥) : False := by
  classical
  have hSM : S ≤ L ⊔ S := le_sup_right
  have hLM : L ≤ L ⊔ S := le_sup_left
  have hgM : g ∈ L ⊔ S := hLM hgL
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hVc : ∀ a ∈ blockV S L, ∀ b ∈ blockV S L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ a ∈ blockV S L, a ^ 2 = 1 := hVel.2
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hML : L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) hSL
  have hXn : ∀ m ∈ L ⊔ S, ∀ x ∈ ⁅blockV S L, L⁆, m * x * m⁻¹ ∈ ⁅blockV S L, L⁆ :=
    fun m hm x hx => conj_mem_commutator' (hMV hm) (hML hm) hx
  let Z₀ : Subgroup G := omegaOneCenterOf (thompsonJ S)
  have hZS : Z₀ ≤ S := (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans
    (thompsonJ_le_self S)
  have hZchar : (Z₀.subgroupOf S).Characteristic :=
    CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans (thompsonJ_le_self S)
      (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S)
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf (thompsonJ S))
  have hZnorm : ∀ s ∈ S, ∀ z ∈ Z₀, s * z * s⁻¹ ∈ Z₀ := by
    intro s hs z hz
    have hN : (Z₀.subgroupOf S).Normal := inferInstance
    have := hN.conj_mem ⟨z, hZS hz⟩ (Subgroup.mem_subgroupOf.2 hz) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hYel : IsElemAbelian 2 (Z₀ ⊔ blockV S L) :=
    CFSG.CGT.PushingUpLit.BHS.isElemAbelian_sup' (B2F.isElemAbelian_omegaOneCenterOf _) hVel
      (fun z hz v hv => hZC z hz v hv)
  have hYc : ∀ a ∈ Z₀ ⊔ blockV S L, ∀ b ∈ Z₀ ⊔ blockV S L, a * b = b * a :=
    fun a ha b hb => CFSG.CGT.PushingUpLit.BHS.isElemAbelian_comm' hYel ha hb
  have hVY : blockV S L ≤ Z₀ ⊔ blockV S L := le_sup_right
  have hgZV : ∀ y ∈ Z₀ ⊔ blockV S L, ⁅g, y⁆ ∈ blockV S L :=
    commutator_mem_sup hVc (fun z hz v hv => hZC z hz v hv) (fun z hz => hZL z hz g hgL)
      (fun v hv => hVn g hgM v hv)
  have hgY : ∀ y ∈ Z₀ ⊔ blockV S L, g * y * g⁻¹ ∈ Z₀ ⊔ blockV S L := by
    intro y hy
    have e : g * y * g⁻¹ = ⁅g, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]; exact (Z₀ ⊔ blockV S L).mul_mem (hVY (hgZV y hy)) hy
  have hgX : ∀ v ∈ blockV S L, ⁅g, v⁆ ∈ ⁅blockV S L, L⁆ := by
    intro v hv
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hv hgL)
  have hkey : ∀ δ : ↥(L ⊔ S), (δ : G) ∈ S → (∀ x ∉ Γ, θ δ x = x) →
      ∀ z ∈ Z₀, g * ⁅(δ : G), z⁆ * g⁻¹ = ⁅(δ : G), z⁆ := by
    intro δ hδS hδfix z hz
    have hδM : (δ : G) ∈ L ⊔ S := δ.2
    have hcomm' : θ ⟨g, hgM⟩ * θ δ = θ δ * θ ⟨g, hgM⟩ := by
      refine (Equiv.Perm.Disjoint.commute ?_)
      intro x
      by_cases hx : x ∈ T
      · right
        exact hδfix x (fun hxΓ => Finset.disjoint_left.1 hTΓ hx hxΓ)
      · left
        exact hgT x hx
    let kM : ↥(L ⊔ S) := (δ * ⟨g, hgM⟩)⁻¹ * (⟨g, hgM⟩ * δ)
    have hkθ : θ kM = 1 := by
      show θ ((δ * ⟨g, hgM⟩)⁻¹ * (⟨g, hgM⟩ * δ)) = 1
      rw [map_mul, map_inv, map_mul, map_mul, hcomm']
      exact inv_mul_cancel _
    have hkdef : (kM : G) = ((δ : G) * g)⁻¹ * (g * (δ : G)) := rfl
    have hkS : (kM : G) ∈ S := hθS kM hkθ
    have hcT : ∀ x ∉ T, θ ⟨g, hgM⟩ x = x := hgT
    have hfΓ : ∀ x ∉ Γ, θ δ x = x := hδfix
    have hzY : z ∈ Z₀ ⊔ blockV S L := Subgroup.mem_sup_left hz
    have hu : ⁅g, z⁆ ∈ blockV S L := hZL z hz g hgL
    have hw0 : ⁅(δ : G), z⁆ ∈ Z₀ := by
      rw [commutatorElement_def]
      exact Z₀.mul_mem (hZnorm δ hδS z hz) (Z₀.inv_mem hz)
    have hwY : ⁅(δ : G), z⁆ ∈ Z₀ ⊔ blockV S L := Subgroup.mem_sup_left hw0
    have hκV : ⁅g, ⁅(δ : G), z⁆⁆ ∈ blockV S L := hZL _ hw0 g hgL
    have hrel := commutator_g_commutator_eq hYc (g := g) (δ := (δ : G)) (z := z)
      (hVY hu) hwY
    set u : G := ⁅g, z⁆ with hudef
    set w : G := ⁅(δ : G), z⁆ with hwdef
    set κ : G := ⁅g, w⁆ with hκdef
    set x' : G := ((δ : G) * g) * ⁅((δ : G) * g)⁻¹ * (g * (δ : G)), z⁆ * ((δ : G) * g)⁻¹ with hx'def
    have hnu := commutator_g_conj_eq hYc hVc hV2 hg3 hgY (fun v hv => hVn g hgM v hv) hzY hu
    have hnκ := commutator_g_conj_eq hYc hVc hV2 hg3 hgY (fun v hv => hVn g hgM v hv) hwY hκV
    have hnu' : ⁅g, g * u * g⁻¹⁆ = u := hnu
    have hnκ' : ⁅g, g * κ * g⁻¹⁆ = κ := hnκ
    have hv₂ : g * u * g⁻¹ ∈ blockV S L := hVn g hgM u hu
    have hv₁ : g * κ * g⁻¹ ∈ blockV S L := hVn g hgM κ hκV
    have huX : u ∈ ⁅blockV S L, L⁆ := by
      have := hgX _ hv₂; rwa [hnu'] at this
    have hκX : κ ∈ ⁅blockV S L, L⁆ := by
      have := hgX _ hv₁; rwa [hnκ'] at this
    have hδu : ⁅(δ : G), u⁆ ∈ ⁅blockV S L, L⁆ := by
      rw [commutatorElement_def]
      exact ⁅blockV S L, L⁆.mul_mem (hXn δ hδM u huX) (⁅blockV S L, L⁆.inv_mem huX)
    have hx'eq : x' = κ * ⁅(δ : G), u⁆⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact hrel.symm
    have hx'X : x' ∈ ⁅blockV S L, L⁆ := by
      rw [hx'eq]; exact ⁅blockV S L, L⁆.mul_mem hκX (⁅blockV S L, L⁆.inv_mem hδu)
    have hx'L : ∀ l ∈ L, l * x' = x' * l := by
      intro l hl
      have hδgM : (δ : G) * g ∈ L ⊔ S := (L ⊔ S).mul_mem hδM hgM
      have hl' : ((δ : G) * g)⁻¹ * l * ((δ : G) * g) ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hML ((L ⊔ S).inv_mem hδgM)) l).1 hl
        simpa using this
      have hc := hXL z hz kM hkθ _ hl'
      rw [hkdef] at hc
      calc l * x' = ((δ : G) * g) * (((δ : G) * g)⁻¹ * l * ((δ : G) * g) *
            ⁅((δ : G) * g)⁻¹ * (g * (δ : G)), z⁆) * ((δ : G) * g)⁻¹ := by
            rw [hx'def]; group
        _ = ((δ : G) * g) * (⁅((δ : G) * g)⁻¹ * (g * (δ : G)), z⁆ *
              (((δ : G) * g)⁻¹ * l * ((δ : G) * g))) * ((δ : G) * g)⁻¹ := by rw [hc]
        _ = x' * l := by rw [hx'def]; group
    have hx'Kr : x' ∈ ⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hx'X, Subgroup.mem_centralizer_iff.2 hx'L⟩
    have hx'1 : π ⟨x', hx'X⟩ = 1 := by
      have : (⟨x', hx'X⟩ : ↥⁅blockV S L, L⁆) ∈ π.ker := by
        rw [hker, Subgroup.mem_subgroupOf]; exact hx'Kr
      exact MonoidHom.mem_ker.1 this
    set v₁ : G := g * κ * g⁻¹ with hv₁def
    have hv₁X : v₁ ∈ ⁅blockV S L, L⁆ := hXn g hgM κ hκX
    have hgv₁ : g * v₁ * g⁻¹ = κ * v₁ := by
      have h : ⁅g, v₁⁆ = κ := hnκ
      rw [commutatorElement_def] at h
      calc g * v₁ * g⁻¹ = (g * v₁ * g⁻¹ * v₁⁻¹) * v₁ := by group
        _ = κ * v₁ := by rw [h]
    have hδu' : (δ : G) * u * (δ : G)⁻¹ = ⁅(δ : G), u⁆ * u := by
      rw [commutatorElement_def]; group
    have hrel' : (g * v₁ * g⁻¹) * u = x' * (((δ : G) * u * (δ : G)⁻¹) * v₁) := by
      have hVu : v₁ * u = u * v₁ := hVc _ hv₁ u hu
      have h1 : κ = x' * ⁅(δ : G), u⁆ := hrel
      calc (g * v₁ * g⁻¹) * u = κ * (v₁ * u) := by rw [hgv₁, mul_assoc]
        _ = κ * (u * v₁) := by rw [hVu]
        _ = (x' * ⁅(δ : G), u⁆) * (u * v₁) := by rw [← h1]
        _ = x' * (((δ : G) * u * (δ : G)⁻¹) * v₁) := by rw [hδu']; group
    obtain ⟨hδuX, hπδu⟩ := pi_commutator_eq_one_of_rel_mul_free π θ hequiv hgM hδM hXn huX hv₁X
      hx'X hx'1 hrel' T Γ hfree hTΓ hcT hfΓ
    have hδuKr : ⁅(δ : G), u⁆ ∈ ⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
      have : (⟨⁅(δ : G), u⁆, hδuX⟩ : ↥⁅blockV S L, L⁆) ∈ π.ker := hπδu
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    have hκKr : κ ∈ ⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
      have h1 : κ = x' * ⁅(δ : G), u⁆ := hrel
      rw [h1]
      exact Subgroup.mul_mem _ hx'Kr hδuKr
    have hgκ : g * κ * g⁻¹ = κ := by
      have := Subgroup.mem_centralizer_iff.1 hκKr.2 g hgL
      calc g * κ * g⁻¹ = κ * g * g⁻¹ := by rw [this]
        _ = κ := by group
    have hgw : g * w * g⁻¹ = κ * w := by rw [hκdef, commutatorElement_def]; group
    have hκ1 : κ = 1 := eq_one_of_conj_eq_mul hgw hgκ (hV2 κ hκV) hm hgm
    rw [hgw, hκ1, one_mul]
  let E : Subgroup G := Subgroup.closure {x | ∃ δ : ↥(L ⊔ S), (δ : G) ∈ S ∧
    (∀ x ∉ Γ, θ δ x = x) ∧ ∃ z ∈ Z₀, x = ⁅(δ : G), z⁆}
  have hEg : ∀ x ∈ E, g * x * g⁻¹ = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨δ, hδS, hδfix, z, hz, rfl⟩ := hy
      exact hkey δ hδS hδfix z hz
    | one => simp
    | mul y z _ _ hy hz =>
      have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [this, hy, hz]
    | inv y _ hy =>
      have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [this, hy]
  have hCS : ⁅Z₀, S⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro z hz s hs
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem (hZS hz) hs) (S.inv_mem (hZS hz))) (S.inv_mem hs)
  have hCE : ⁅Z₀, S⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro z hz s hs
    obtain ⟨j, hjJ, δ, hδS, hδfix, rfl⟩ := hdecomp s hs
    have hzj : Commute (j : G) z :=
      (Subgroup.mem_centralizer_iff.1
        ((CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf _ hz).2) j hjJ)
    have hjz : j * z⁻¹ = z⁻¹ * j := hzj.inv_right.eq
    have hz' : ⁅z, (δ : G) * j⁆ = ⁅z, (δ : G)⁆ := by
      calc ⁅z, (δ : G) * j⁆ = z * (δ : G) * (j * z⁻¹) * j⁻¹ * (δ : G)⁻¹ := by
            rw [commutatorElement_def]; group
        _ = z * (δ : G) * (z⁻¹ * j) * j⁻¹ * (δ : G)⁻¹ := by rw [hjz]
        _ = ⁅z, (δ : G)⁆ := by rw [commutatorElement_def]; group
    rw [hz', ← commutatorElement_inv]
    exact E.inv_mem (Subgroup.subset_closure ⟨δ, hδS, hδfix, z, hz, rfl⟩)
  have hCchar : ((⁅Z₀, S⁆).subgroupOf S).Characteristic :=
    characteristic_commutator_subgroupOf hZS hZchar
  have hgN : g ∈ Subgroup.normalizer (S : Set G) :=
    mem_normalizer_of_char_commute hA hCS hne hCchar hgM (fun x hx => hEg x (hCE hx))
  exact hcN (theta_mem_normalizer_W θ ⟨g, hgM⟩ hgN)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
