module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltBasic

open BlocksChief

section Quasisimple
variable {G H : Type*} [Group G] [Group H]

theorem ker_le_center_of_quasisimple (hG : CFSG.IsQuasisimple G) (f : G →* H) (hf : ∃ g, f g ≠ 1) :
    f.ker ≤ Subgroup.center G := by
  obtain ⟨hperf, hsimp, -⟩ := hG
  have hperf' : commutator G = ⊤ := hperf.commutator_eq_top
  haveI hM : (f.ker.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (f.ker.map (QuotientGroup.mk' (Subgroup.center G))) with h0 | h1
  · intro n hn
    have : QuotientGroup.mk' (Subgroup.center G) n ∈
        f.ker.map (QuotientGroup.mk' (Subgroup.center G)) := ⟨n, hn, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).1 this
  · exfalso
    obtain ⟨g₀, hg₀⟩ := hf
    have hdec : ∀ g : G, ∃ z ∈ Subgroup.center G, f g = f z := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center G) g ∈
          f.ker.map (QuotientGroup.mk' (Subgroup.center G)) := by rw [h1]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := hg
      have hz : n⁻¹ * g ∈ Subgroup.center G := by
        have := (QuotientGroup.eq (s := Subgroup.center G)).1 hng
        exact this
      refine ⟨n⁻¹ * g, hz, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hn, inv_one, one_mul]
    have hcomm : commutator G ≤ f.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g _ h _
      obtain ⟨z₁, hz₁, he₁⟩ := hdec g
      obtain ⟨z₂, hz₂, he₂⟩ := hdec h
      rw [MonoidHom.mem_ker, map_commutatorElement, he₁, he₂, ← map_commutatorElement]
      have : ⁅z₁, z₂⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 hz₂ z₁)
      rw [this, map_one]
    rw [hperf'] at hcomm
    exact hg₀ (hcomm (Subgroup.mem_top g₀))

theorem comap_center_eq_center [Group.IsPerfect G] (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) : (Subgroup.center H).comap f = Subgroup.center G := by
  ext k
  constructor
  · intro hk
    have hk' : f k ∈ Subgroup.center H := hk
    have : QuotientGroup.mk' (Subgroup.center G) k ∈ Subgroup.center (G ⧸ Subgroup.center G) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
      rw [← map_mul, ← map_mul]
      apply (QuotientGroup.eq (s := Subgroup.center G)).2
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
        Subgroup.mem_center_iff.1 hk' (f g), inv_mul_cancel]
    rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff k).1 this
  · intro hk
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := hf h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hk g]

theorem nonempty_quotCenter_equiv [Group.IsPerfect G] (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) :
    Nonempty ((G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H)) := by
  set F : G →* H ⧸ Subgroup.center H := (QuotientGroup.mk' (Subgroup.center H)).comp f with hFdef
  have hF : Function.Surjective F := (QuotientGroup.mk'_surjective _).comp hf
  have hFker : F.ker = Subgroup.center G := by
    rw [← comap_center_eq_center f hf hker]
    ext x
    simp [hFdef, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hFker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective F hF)⟩

end Quasisimple

theorem eq_of_card_two {G : Type*} [Group G] (hG : Nat.card G = 2) (x y : G) (hx : x ≠ 1)
    (hy : y ≠ 1) : x = y := by
  obtain ⟨u, v, huv, hs⟩ := Nat.card_eq_two_iff.1 hG
  have hmem : ∀ g : G, g = u ∨ g = v := fun g => by
    have : g ∈ ({u, v} : Set G) := by rw [hs]; exact Set.mem_univ g
    simpa using this
  by_contra hxy
  rcases hmem 1 with h1 | h1 <;> rcases hmem x with h2 | h2 <;> rcases hmem y with h3 | h3 <;>
    first | exact hx (h2.trans h1.symm) | exact hy (h3.trans h1.symm) | exact hxy (h2.trans h3.symm)

theorem chiefFactorIso_comp {G : Type*} [Group G] {A A' N N' : Type*} [Group A] [Group A']
    [AddCommGroup N] [AddCommGroup N'] {L U V : Subgroup G} {ρ : ↥L →* A} {act : A → N → N}
    (hiso : ChiefFactorIso L U V ρ act) (f : A →* A') (β : N ≃+ N') (act' : A' → N' → N')
    (hact : ∀ a n, β (act a n) = act' (f a) (β n)) :
    ChiefFactorIso L U V (f.comp ρ) act' := by
  obtain ⟨φ, hs, hk, he⟩ := hiso
  refine ⟨(AddEquiv.toMultiplicative β).toMonoidHom.comp φ, ?_, fun u => ?_, fun ℓ u u' hu' => ?_⟩
  · exact (AddEquiv.toMultiplicative β).surjective.comp hs
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hk u
  · show (AddEquiv.toMultiplicative β) (φ u') = Multiplicative.ofAdd (act' (f (ρ ℓ))
      (Multiplicative.toAdd ((AddEquiv.toMultiplicative β) (φ u))))
    rw [he ℓ u u' hu']
    show Multiplicative.ofAdd (β (act (ρ ℓ) (Multiplicative.toAdd (φ u)))) =
      Multiplicative.ofAdd (act' (f (ρ ℓ)) (β (Multiplicative.toAdd (φ u))))
    rw [hact]

section Model
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

noncomputable def barLift {A : Type*} [Group A] (θ : ↥K →* A)
    (hθ : ∀ k : ↥K, (k : X) ∈ W → θ k = 1) : ↥(bar W K) →* A :=
  (toBar W K).liftOfSurjective (toBar_surjective W K) ⟨θ, fun k hk => by
    rw [MonoidHom.mem_ker, toBar_eq_one_iff] at hk
    exact hθ k hk⟩

theorem barLift_toBar {A : Type*} [Group A] (θ : ↥K →* A)
    (hθ : ∀ k : ↥K, (k : X) ∈ W → θ k = 1) (k : ↥K) : barLift θ hθ (toBar W K k) = θ k :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k

theorem exists_iso_of_alt (hR : Red28 W K S) {m : ℕ} (hm : 5 ≤ m)
    (θ : ↥K →* ↥(alternatingGroup (Fin m))) (hsurj : Function.Surjective θ)
    (hθ : ∀ k : ↥K, (k : X) ∈ W → θ k = 1) :
    ∃ e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin m)),
      ∀ k : ↥K, e (QuotientGroup.mk (toBar W K k)) = θ k := by
  set θ' := barLift (W := W) θ hθ with hθ'
  have hcomp : ∀ k : ↥K, θ' (toBar W K k) = θ k := barLift_toBar θ hθ
  have hsurj' : Function.Surjective θ' := by
    intro a
    obtain ⟨k, rfl⟩ := hsurj a
    exact ⟨toBar W K k, hcomp k⟩
  have hcard : 4 ≤ Nat.card (Fin m) := by simp; omega
  have : Nontrivial ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  have hnt : ∃ g, θ' g ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(alternatingGroup (Fin m)))
    obtain ⟨g, rfl⟩ := hsurj' x
    exact ⟨g, hx⟩
  have hker : θ'.ker ≤ Subgroup.center ↥(bar W K) :=
    ker_le_center_of_quasisimple hR.quasi θ' hnt
  have hcen : Subgroup.center ↥(bar W K) ≤ θ'.ker := by
    intro z hz
    have : θ' z ∈ Subgroup.center ↥(alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨g, rfl⟩ := hsurj' a
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
    rw [alternatingGroup.center_eq_bot hcard, Subgroup.mem_bot] at this
    exact this
  have hkereq : θ'.ker = Subgroup.center ↥(bar W K) := le_antisymm hker hcen
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hkereq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ' hsurj'), fun k => ?_⟩
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rw [← hcomp k]
  rfl

theorem theta_ker (hR : Red28 W K S) (hZ : Subgroup.center ↥(bar W K) = ⊥) {m : ℕ} (hm : 5 ≤ m)
    (θ : ↥K →* ↥(alternatingGroup (Fin m))) (hsurj : Function.Surjective θ)
    (hθ : ∀ k : ↥K, (k : X) ∈ W → θ k = 1) : ∀ k : ↥K, θ k = 1 → (k : X) ∈ W := by
  set θ' := barLift (W := W) θ hθ with hθ'
  have hcomp : ∀ k : ↥K, θ' (toBar W K k) = θ k := barLift_toBar θ hθ
  have hsurj' : Function.Surjective θ' := by
    intro a
    obtain ⟨k, rfl⟩ := hsurj a
    exact ⟨toBar W K k, hcomp k⟩
  have : Nontrivial ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  have hnt : ∃ g, θ' g ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(alternatingGroup (Fin m)))
    obtain ⟨g, rfl⟩ := hsurj' x
    exact ⟨g, hx⟩
  have hker : θ'.ker ≤ Subgroup.center ↥(bar W K) :=
    ker_le_center_of_quasisimple hR.quasi θ' hnt
  intro k hk
  have h1 : toBar W K k ∈ θ'.ker := by
    rw [MonoidHom.mem_ker, hcomp]; exact hk
  have h2 := hker h1
  rw [hZ, Subgroup.mem_bot] at h2
  exact (toBar_eq_one_iff k).1 h2

end Model

section Ind
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

@[expose] noncomputable def indOf {b : X} (hN : b ∈ Subgroup.normalizer (K : Set X)) :
    MulAut ↥(bar W K) :=
  (bar W K).normalizerMonoidHom ⟨QuotientGroup.mk b,
    Subgroup.le_normalizer_map (QuotientGroup.mk' W) ⟨b, hN, rfl⟩⟩

theorem indOf_toBar {b : X} (hN : b ∈ Subgroup.normalizer (K : Set X)) (k k' : ↥K)
    (hk' : (k' : X) = b * k * b⁻¹) : indOf (W := W) hN (toBar W K k) = toBar W K k' := by
  apply Subtype.ext
  show (QuotientGroup.mk b : X ⧸ W) * QuotientGroup.mk (k : X) * (QuotientGroup.mk b)⁻¹ =
    QuotientGroup.mk (k' : X)
  rw [hk']
  simp

theorem indOf_mem {b : X} (hN : b ∈ Subgroup.normalizer (K : Set X)) (hbS : b ∈ S) :
    indOf (W := W) hN ∈ indAut W K S :=
  ⟨⟨QuotientGroup.mk b, Subgroup.le_normalizer_map (QuotientGroup.mk' W) ⟨b, hN, rfl⟩⟩,
    Subgroup.mem_subgroupOf.2 ⟨b, hbS, rfl⟩, rfl⟩

theorem conj_mem_K {b : X} (hN : b ∈ Subgroup.normalizer (K : Set X)) {k : X} (hk : k ∈ K) :
    b * k * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hN k).1 hk

theorem comm_mem_of_indOf_eq_one {b : X} (hN : b ∈ Subgroup.normalizer (K : Set X))
    (h1 : indOf (W := W) hN = 1) : ∀ k ∈ K, ⁅b, k⁆ ∈ W := by
  intro k hk
  have h0 := indOf_toBar (W := W) hN ⟨k, hk⟩ ⟨b * k * b⁻¹, conj_mem_K hN hk⟩ rfl
  rw [h1, MulAut.one_apply] at h0
  have h2 : (QuotientGroup.mk (k : X) : X ⧸ W) = QuotientGroup.mk (b * k * b⁻¹) :=
    congrArg Subtype.val h0
  have h3 : (k : X)⁻¹ * (b * k * b⁻¹) ∈ W := QuotientGroup.eq.1 h2
  have h4 := Subgroup.Normal.conj_mem inferInstance _ h3 (k : X)
  have h5 : ⁅b, k⁆ = (k : X) * ((k : X)⁻¹ * (b * k * b⁻¹)) * (k : X)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h5]
  exact h4

theorem comm_mem_of_indOf_eq {b c : X} (hb : b ∈ Subgroup.normalizer (K : Set X))
    (hc : c ∈ Subgroup.normalizer (K : Set X)) (h1 : indOf (W := W) hb = indOf (W := W) hc) :
    ∀ k ∈ K, ⁅b⁻¹ * c, k⁆ ∈ W := by
  intro k hk
  have e1 := indOf_toBar (W := W) hb ⟨k, hk⟩ ⟨b * k * b⁻¹, conj_mem_K hb hk⟩ rfl
  have e2 := indOf_toBar (W := W) hc ⟨k, hk⟩ ⟨c * k * c⁻¹, conj_mem_K hc hk⟩ rfl
  rw [h1, e2] at e1
  have h2 : (QuotientGroup.mk (c * k * c⁻¹) : X ⧸ W) = QuotientGroup.mk (b * k * b⁻¹) :=
    congrArg Subtype.val e1
  have h3 : (c * k * c⁻¹)⁻¹ * (b * k * b⁻¹) ∈ W := QuotientGroup.eq.1 h2
  have h4 := Subgroup.Normal.conj_mem inferInstance _ h3 (b⁻¹ * (c * k * c⁻¹))
  have h5 : ⁅b⁻¹ * c, k⁆ = ((b⁻¹ * (c * k * c⁻¹)) * ((c * k * c⁻¹)⁻¹ * (b * k * b⁻¹)) *
      (b⁻¹ * (c * k * c⁻¹))⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h5]
  exact W.inv_mem h4

theorem S_cases_of_card_two (h : Setup28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (hS2 : Nat.card ↥(indAut W K S) = 2) :
    ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S := by
  intro s hsS
  have hNa := h.hN haS
  have hNs := h.hN hsS
  have hα1 : indOf (W := W) hNa ≠ 1 := fun h1 => hna ⟨haS, comm_mem_of_indOf_eq_one hNa h1⟩
  by_cases hs1 : indOf (W := W) hNs = 1
  · exact Or.inl ⟨hsS, comm_mem_of_indOf_eq_one hNs hs1⟩
  · right
    have heq := eq_of_card_two hS2 ⟨indOf (W := W) hNs, indOf_mem hNs hsS⟩
      ⟨indOf (W := W) hNa, indOf_mem hNa haS⟩ (fun h' => hs1 (congrArg Subtype.val h'))
      (fun h' => hα1 (congrArg Subtype.val h'))
    exact ⟨S.mul_mem (S.inv_mem haS) hsS,
      comm_mem_of_indOf_eq hNa hNs (congrArg Subtype.val heq).symm⟩

end Ind

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltBasic
