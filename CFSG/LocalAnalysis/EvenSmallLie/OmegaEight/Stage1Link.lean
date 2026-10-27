module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.Stage2 (urRows)

variable {G : Type*} [Group G]

structure LinkFacts (ε : Eps) (L U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p u : Fin 6 → G) :
    Prop where
  Q_le_U : Q ≤ U
  U_le_P : U ≤ P
  P_eq : P = L ⊓ normalizer (Q : Set G)
  U_pgroup : IsPGroup 2 U
  center_U : ∀ x ∈ U, (∀ y ∈ U, x * y = y * x) → x = 1 ∨ x = a
  ψ_add : ∀ v w, ψ (v + w) = ψ v * ψ w
  ψ_inj : Function.Injective ψ
  ψ_mem : ∀ v, ψ v ∈ Q
  mem_ψ : ∀ x ∈ Q, ∃ v, ψ v = x
  a_eq : a = ψ (Pi.single 0 1)
  p_mem : ∀ i, p i ∈ P
  p_act : ∀ i v, p i * ψ v * (p i)⁻¹ = ψ (genMat ε i *ᵥ v)
  P_le : P ≤ closure ((Q : Set G) ∪ Set.range p)
  card_P : Nat.card P = 64 * (oBound ε / 2)
  S5 : ∀ A : Subgroup G, A ≤ U → (∀ x ∈ U, ∀ y ∈ A, x * y * x⁻¹ ∈ A) →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) → Nat.card A = 64 →
    ∃ l ∈ L, (∀ x ∈ A, l * x * l⁻¹ ∈ A) ∧ l * a * l⁻¹ ≠ a
  u_mem : ∀ k, u k ∈ U
  u_act : ∀ k v, u k * ψ v * (u k)⁻¹ = ψ (toMat 6 6 (urRows ε k) *ᵥ v)
  U_le : U ≤ closure ((Q : Set G) ∪ Set.range u)
  U_max : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U
  cent_Q : ∀ l ∈ L, (∀ q ∈ Q, l * q = q * l) → l ∈ Q

namespace LinkFacts

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}

theorem radicalData (h : LinkFacts ε L U Q P a ψ p u) (hodd : InvolutionsInOddPart L) :
    RadicalData ε L U Q P a ψ p where
  odd := hodd
  Q_le_U := h.Q_le_U
  U_le_P := h.U_le_P
  P_eq := h.P_eq
  U_pgroup := h.U_pgroup
  center_U := h.center_U
  ψ_add := h.ψ_add
  ψ_inj := h.ψ_inj
  ψ_mem := h.ψ_mem
  mem_ψ := h.mem_ψ
  a_eq := h.a_eq
  p_mem := h.p_mem
  p_act := h.p_act
  P_le := h.P_le
  card_P := h.card_P
  S5 := h.S5

end LinkFacts

section Transport

variable {X : Type*} [Group X] {L : Subgroup G} {L' : Subgroup X} (θ : L ≃* L')

@[expose] def pull (H' : Subgroup X) : Subgroup G :=
  ((H'.subgroupOf L').comap θ.toMonoidHom).map L.subtype

@[expose] noncomputable def pullE (x : X) (hx : x ∈ L') : G := (θ.symm ⟨x, hx⟩ : G)

variable {θ}

theorem mem_pull {H' : Subgroup X} {g : G} :
    g ∈ pull θ H' ↔ ∃ hg : g ∈ L, ((θ ⟨g, hg⟩ : L') : X) ∈ H' := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem pull_le_L (H' : Subgroup X) : pull θ H' ≤ L := fun _ hg => (mem_pull.1 hg).1

theorem pull_mono {H' K' : Subgroup X} (h : H' ≤ K') : pull θ H' ≤ pull θ K' := fun _ hg => by
  obtain ⟨hgL, hg'⟩ := mem_pull.1 hg
  exact mem_pull.2 ⟨hgL, h hg'⟩

theorem pullE_mem_L {x : X} (hx : x ∈ L') : pullE θ x hx ∈ L := (θ.symm ⟨x, hx⟩).2

theorem theta_pullE {x : X} (hx : x ∈ L') :
    θ ⟨pullE θ x hx, pullE_mem_L hx⟩ = ⟨x, hx⟩ := by
  simp [pullE]

theorem pullE_mem_pull {H' : Subgroup X} {x : X} (hx : x ∈ L') :
    pullE θ x hx ∈ pull θ H' ↔ x ∈ H' := by
  rw [mem_pull]
  constructor
  · rintro ⟨_, h⟩
    rwa [theta_pullE] at h
  · intro h
    exact ⟨pullE_mem_L hx, by rw [theta_pullE]; exact h⟩

theorem pullE_mul {x y : X} (hx : x ∈ L') (hy : y ∈ L') :
    pullE θ (x * y) (mul_mem hx hy) = pullE θ x hx * pullE θ y hy := by
  simp only [pullE]
  rw [show (⟨x * y, mul_mem hx hy⟩ : L') = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
  rfl

theorem pullE_inv {x : X} (hx : x ∈ L') : pullE θ x⁻¹ (inv_mem hx) = (pullE θ x hx)⁻¹ := by
  simp only [pullE]
  rw [show (⟨x⁻¹, inv_mem hx⟩ : L') = (⟨x, hx⟩)⁻¹ from rfl, map_inv]
  rfl

theorem pullE_one : pullE θ (1 : X) (one_mem _) = 1 := by
  simp only [pullE]
  rw [show (⟨1, one_mem _⟩ : L') = 1 from rfl, map_one]
  rfl

theorem pullE_injective {x y : X} (hx : x ∈ L') (hy : y ∈ L') (h : pullE θ x hx = pullE θ y hy) :
    x = y := by
  have h1 : θ.symm ⟨x, hx⟩ = θ.symm ⟨y, hy⟩ := Subtype.ext h
  exact congrArg Subtype.val (θ.symm.injective h1)

theorem exists_pullE {g : G} (hg : g ∈ L) : ∃ x : X, ∃ hx : x ∈ L', pullE θ x hx = g :=
  ⟨θ ⟨g, hg⟩, (θ ⟨g, hg⟩).2, by simp [pullE]⟩


theorem theta_mem_of_mem_pull {H' : Subgroup X} {g : G} (hg : g ∈ pull θ H') :
    ((θ ⟨g, pull_le_L H' hg⟩ : L') : X) ∈ H' := by
  obtain ⟨_, h⟩ := mem_pull.1 hg
  exact h

theorem pullE_congr {x y : X} (hxy : x = y) (hx : x ∈ L') (hy : y ∈ L') :
    pullE θ x hx = pullE θ y hy := by
  subst hxy
  rfl

theorem pullE_conj {x y : X} (hx : x ∈ L') (hy : y ∈ L') :
    pullE θ (x * y * x⁻¹) (mul_mem (mul_mem hx hy) (inv_mem hx)) =
      pullE θ x hx * pullE θ y hy * (pullE θ x hx)⁻¹ := by
  rw [pullE_mul (mul_mem hx hy) (inv_mem hx), pullE_mul hx hy, pullE_inv hx]

theorem theta_mul {g h : G} (hg : g ∈ L) (hh : h ∈ L) :
    ((θ ⟨g * h, mul_mem hg hh⟩ : L') : X) = (θ ⟨g, hg⟩ : X) * (θ ⟨h, hh⟩ : X) := by
  rw [show (⟨g * h, mul_mem hg hh⟩ : L) = ⟨g, hg⟩ * ⟨h, hh⟩ from rfl, map_mul]
  rfl

theorem theta_inv {g : G} (hg : g ∈ L) :
    ((θ ⟨g⁻¹, inv_mem hg⟩ : L') : X) = ((θ ⟨g, hg⟩ : L') : X)⁻¹ := by
  rw [show (⟨g⁻¹, inv_mem hg⟩ : L) = (⟨g, hg⟩)⁻¹ from rfl, map_inv]
  rfl

theorem theta_injective {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (e : ((θ ⟨g, hg⟩ : L') : X) = (θ ⟨h, hh⟩ : X)) : g = h :=
  congrArg Subtype.val (θ.injective (Subtype.ext e))

@[expose] noncomputable def pullHom (θ : L ≃* L') (H' : Subgroup X) : pull θ H' →* H' where
  toFun g := ⟨(θ ⟨g, pull_le_L H' g.2⟩ : X), theta_mem_of_mem_pull g.2⟩
  map_one' := by
    apply Subtype.ext
    change ((θ ⟨1, one_mem _⟩ : L') : X) = 1
    rw [show (⟨1, one_mem _⟩ : L) = 1 from rfl, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    exact theta_mul (pull_le_L H' g.2) (pull_le_L H' h.2)

@[expose] noncomputable def pullEquiv {H' : Subgroup X} (hH : H' ≤ L') : pull θ H' ≃* H' :=
  MulEquiv.ofBijective (pullHom θ H')
    ⟨fun g h e => Subtype.ext (theta_injective (θ := θ) (pull_le_L H' g.2) (pull_le_L H' h.2)
        (by have h1 := congrArg Subtype.val e; exact h1)),
      fun x => ⟨⟨pullE θ x (hH x.2), (pullE_mem_pull (hH x.2)).2 x.2⟩, by
        apply Subtype.ext
        change ((θ ⟨pullE θ x (hH x.2), _⟩ : L') : X) = x
        rw [theta_pullE]⟩⟩

theorem card_pull {H' : Subgroup X} (hH : H' ≤ L') : Nat.card (pull θ H') = Nat.card H' :=
  Nat.card_congr (pullEquiv hH).toEquiv

theorem pull_symm_pull {A : Subgroup G} (hA : A ≤ L) : pull θ (pull θ.symm A) = A := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgL, h⟩ := mem_pull.1 hg
    obtain ⟨_, h'⟩ := mem_pull.1 h
    simpa using h'
  · intro hg
    refine mem_pull.2 ⟨hA hg, mem_pull.2 ⟨(θ ⟨g, hA hg⟩).2, ?_⟩⟩
    simpa using hg

theorem mem_pull_symm {A : Subgroup G} {x : X} :
    x ∈ pull θ.symm A ↔ ∃ hx : x ∈ L', pullE θ x hx ∈ A := by
  rw [mem_pull]
  rfl

theorem pull_closure_le {S' : Set X} (hS : S' ⊆ L') {T : Set G}
    (hT : ∀ x (hx : x ∈ S'), pullE θ x (hS hx) ∈ T) : pull θ (closure S') ≤ closure T := by
  intro g hg
  obtain ⟨hgL, h⟩ := mem_pull.1 hg
  have key : ∀ x ∈ closure S', ∀ hx : x ∈ L', pullE θ x hx ∈ closure T := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun _ => subset_closure (hT x hx)
    | one => exact fun _ => by rw [pullE_one]; exact one_mem _
    | mul x y hx hy ihx ihy =>
      intro hxy
      have hxL : x ∈ L' := (closure_le L').2 hS hx
      have hyL : y ∈ L' := (closure_le L').2 hS hy
      rw [pullE_mul hxL hyL]
      exact mul_mem (ihx hxL) (ihy hyL)
    | inv x hx ihx =>
      intro hxi
      have hxL : x ∈ L' := (closure_le L').2 hS hx
      rw [pullE_inv hxL]
      exact inv_mem (ihx hxL)
  have := key _ h (θ ⟨g, hgL⟩).2
  simpa [pullE] using this

theorem theta_conj {g h : G} (hg : g ∈ L) (hh : h ∈ L) :
    ((θ ⟨g * h * g⁻¹, mul_mem (mul_mem hg hh) (inv_mem hg)⟩ : L') : X) =
      (θ ⟨g, hg⟩ : X) * (θ ⟨h, hh⟩ : X) * ((θ ⟨g, hg⟩ : L') : X)⁻¹ := by
  rw [theta_mul (mul_mem hg hh) (inv_mem hg), theta_mul hg hh, theta_inv hg]

theorem pull_inf_normalizer {Q' : Subgroup X} (hQ : Q' ≤ L') :
    pull θ (L' ⊓ normalizer (Q' : Set X)) = L ⊓ normalizer (pull θ Q' : Set G) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgL, hgN⟩ := mem_pull.1 hg
    refine ⟨hgL, mem_normalizer_iff.2 fun h => ?_⟩
    by_cases hhL : h ∈ L
    · have hN := mem_normalizer_iff.1 hgN.2 (θ ⟨h, hhL⟩ : X)
      rw [mem_pull, mem_pull]
      constructor
      · rintro ⟨_, hh⟩
        refine ⟨mul_mem (mul_mem hgL hhL) (inv_mem hgL), ?_⟩
        rw [theta_conj hgL hhL]
        exact hN.1 hh
      · rintro ⟨_, hh⟩
        refine ⟨hhL, hN.2 ?_⟩
        rw [← theta_conj hgL hhL]
        exact hh
    · constructor
      · intro hh
        exact absurd (pull_le_L _ hh) hhL
      · intro hh
        exfalso
        apply hhL
        have := mul_mem (mul_mem (inv_mem hgL) (pull_le_L _ hh)) hgL
        simpa [mul_assoc] using this
  · rintro ⟨hgL, hgN⟩
    refine mem_pull.2 ⟨hgL, (θ ⟨g, hgL⟩).2, mem_normalizer_iff.2 fun x => ?_⟩
    by_cases hxL : x ∈ L'
    · obtain ⟨h, hhL, rfl⟩ : ∃ h : G, ∃ hh : h ∈ L, ((θ ⟨h, hh⟩ : L') : X) = x :=
        ⟨pullE θ x hxL, pullE_mem_L hxL, by rw [theta_pullE]⟩
      have hN := mem_normalizer_iff.1 hgN h
      rw [← theta_conj hgL hhL]
      constructor
      · intro hx
        have := hN.1 (mem_pull.2 ⟨hhL, hx⟩)
        exact theta_mem_of_mem_pull this
      · intro hx
        have := hN.2 (mem_pull.2 ⟨mul_mem (mul_mem hgL hhL) (inv_mem hgL), hx⟩)
        exact theta_mem_of_mem_pull this
    · constructor
      · intro hx
        exact absurd (hQ hx) hxL
      · intro hx
        exfalso
        apply hxL
        have h1 := mul_mem (mul_mem (inv_mem (θ ⟨g, hgL⟩).2) (hQ hx)) (θ ⟨g, hgL⟩).2
        simpa [mul_assoc] using h1


theorem theta_comm {g h : G} (hg : g ∈ L) (hh : h ∈ L) (e : g * h = h * g) :
    ((θ ⟨g, hg⟩ : L') : X) * (θ ⟨h, hh⟩ : X) = (θ ⟨h, hh⟩ : X) * (θ ⟨g, hg⟩ : X) := by
  rw [← theta_mul hg hh, ← theta_mul hh hg]
  have : (⟨g * h, mul_mem hg hh⟩ : L) = ⟨h * g, mul_mem hh hg⟩ := Subtype.ext e
  rw [this]

theorem pullE_theta {g : G} (hg : g ∈ L) : pullE θ (θ ⟨g, hg⟩ : X) (θ ⟨g, hg⟩).2 = g := by
  simp [pullE]

theorem eq_pullE_of_theta {g : G} (hg : g ∈ L) {x : X} (hx : x ∈ L')
    (e : ((θ ⟨g, hg⟩ : L') : X) = x) : g = pullE θ x hx := by
  subst e
  exact (pullE_theta hg).symm

end Transport


namespace LinkFacts

variable {X : Type*} [Group X] {L : Subgroup G} {L' : Subgroup X} {ε : Eps}
  {U' Q' P' : Subgroup X} {a' : X} {ψ' : V6 → X} {p' u' : Fin 6 → X}

theorem P_le_L (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') : P' ≤ L' := by
  rw [h.P_eq]
  exact inf_le_left

theorem U_le_L (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') : U' ≤ L' := h.U_le_P.trans h.P_le_L

theorem Q_le_L (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') : Q' ≤ L' := h.Q_le_U.trans h.U_le_L

theorem ψ_mem_L (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') (v : V6) : ψ' v ∈ L' :=
  h.Q_le_L (h.ψ_mem v)

theorem a_mem_L (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') : a' ∈ L' := h.a_eq ▸ h.ψ_mem_L _

theorem p_mem_L (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') (i : Fin 6) : p' i ∈ L' :=
  h.P_le_L (h.p_mem i)

theorem u_mem_L (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') (k : Fin 6) : u' k ∈ L' :=
  h.U_le_L (h.u_mem k)

theorem transport (h : LinkFacts ε L' U' Q' P' a' ψ' p' u') (θ : L ≃* L') :
    LinkFacts ε L (pull θ U') (pull θ Q') (pull θ P') (pullE θ a' h.a_mem_L)
      (fun v => pullE θ (ψ' v) (h.ψ_mem_L v)) (fun i => pullE θ (p' i) (h.p_mem_L i))
      (fun k => pullE θ (u' k) (h.u_mem_L k)) where
  Q_le_U := pull_mono h.Q_le_U
  U_le_P := pull_mono h.U_le_P
  P_eq := by
    rw [h.P_eq]
    exact pull_inf_normalizer h.Q_le_L
  U_pgroup := h.U_pgroup.of_equiv (pullEquiv h.U_le_L).symm
  center_U := by
    intro x hx hc
    obtain ⟨hxL, hx'⟩ := mem_pull.1 hx
    have hc' : ∀ y ∈ U', ((θ ⟨x, hxL⟩ : L') : X) * y = y * (θ ⟨x, hxL⟩ : X) := by
      intro y hy
      have hyL := h.U_le_L hy
      have e := theta_comm (θ := θ) hxL (pullE_mem_L hyL)
        (hc _ ((pullE_mem_pull hyL).2 hy))
      rwa [theta_pullE] at e
    rcases h.center_U _ hx' hc' with h1 | h1
    · left
      rw [eq_pullE_of_theta hxL (one_mem _) h1, pullE_one]
    · right
      exact eq_pullE_of_theta hxL _ h1
  ψ_add v w := by
    rw [pullE_congr (h.ψ_add v w) _ (mul_mem (h.ψ_mem_L v) (h.ψ_mem_L w)), pullE_mul]
  ψ_inj v w e := h.ψ_inj (pullE_injective _ _ e)
  ψ_mem v := (pullE_mem_pull _).2 (h.ψ_mem v)
  mem_ψ x hx := by
    obtain ⟨hxL, hx'⟩ := mem_pull.1 hx
    obtain ⟨v, hv⟩ := h.mem_ψ _ hx'
    exact ⟨v, (eq_pullE_of_theta hxL (h.ψ_mem_L v) hv.symm).symm⟩
  a_eq := pullE_congr h.a_eq _ _
  p_mem i := (pullE_mem_pull _).2 (h.p_mem i)
  p_act i v := by
    rw [← pullE_conj]
    exact pullE_congr (h.p_act i v) _ _
  P_le := by
    refine (pull_mono h.P_le).trans (pull_closure_le ?_ ?_)
    · rintro x (hx | ⟨i, rfl⟩)
      · exact h.Q_le_L hx
      · exact h.p_mem_L i
    · rintro x (hx | ⟨i, rfl⟩)
      · exact Or.inl ((pullE_mem_pull _).2 hx)
      · exact Or.inr ⟨i, rfl⟩
  card_P := by rw [card_pull h.P_le_L, h.card_P]
  S5 := by
    intro A hAU hAn hAc hA2 hA64
    have hAL : A ≤ L := hAU.trans (pull_le_L _)
    have hA'L : pull θ.symm A ≤ L' := pull_le_L _
    have memA' : ∀ x (hx : x ∈ L'), x ∈ pull θ.symm A ↔ pullE θ x hx ∈ A := fun x hx => by
      rw [mem_pull_symm]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩
    obtain ⟨l', hl'L, hl'A, hl'a⟩ := h.S5 (pull θ.symm A)
      (fun x hx => by
        obtain ⟨hxL, hxA⟩ := mem_pull_symm.1 hx
        exact (pullE_mem_pull hxL).1 (hAU hxA))
      (fun x hx y hy => by
        obtain ⟨hyL, hyA⟩ := mem_pull_symm.1 hy
        have hxL := h.U_le_L hx
        refine (memA' _ (mul_mem (mul_mem hxL hyL) (inv_mem hxL))).2 ?_
        rw [pullE_conj hxL hyL]
        exact hAn _ ((pullE_mem_pull hxL).2 hx) _ hyA)
      (fun x hx y hy => by
        obtain ⟨hxL, hxA⟩ := mem_pull_symm.1 hx
        obtain ⟨hyL, hyA⟩ := mem_pull_symm.1 hy
        apply pullE_injective (θ := θ) (mul_mem hxL hyL) (mul_mem hyL hxL)
        rw [pullE_mul hxL hyL, pullE_mul hyL hxL]
        exact hAc _ hxA _ hyA)
      (fun x hx => by
        obtain ⟨hxL, hxA⟩ := mem_pull_symm.1 hx
        apply pullE_injective (θ := θ) (mul_mem hxL hxL) (one_mem _)
        rw [pullE_mul hxL hxL, pullE_one]
        exact hA2 _ hxA)
      (by rw [← hA64, ← card_pull (θ := θ) hA'L, pull_symm_pull hAL])
    refine ⟨pullE θ l' hl'L, pullE_mem_L _, fun x hx => ?_, fun e => hl'a ?_⟩
    · obtain ⟨x', hx'L, rfl⟩ := exists_pullE (θ := θ) (hAL hx)
      rw [← pullE_conj]
      exact (memA' _ _).1 (hl'A x' ((memA' x' hx'L).2 hx))
    · rw [← pullE_conj] at e
      exact pullE_injective _ _ e
  u_mem k := (pullE_mem_pull _).2 (h.u_mem k)
  u_act k v := by
    rw [← pullE_conj]
    exact pullE_congr (h.u_act k v) _ _
  U_le := by
    refine (pull_mono h.U_le).trans (pull_closure_le ?_ ?_)
    · rintro x (hx | ⟨k, rfl⟩)
      · exact h.Q_le_L hx
      · exact h.u_mem_L k
    · rintro x (hx | ⟨k, rfl⟩)
      · exact Or.inl ((pullE_mem_pull _).2 hx)
      · exact Or.inr ⟨k, rfl⟩
  U_max := by
    intro V hVL hV2 hUV
    have hV'L : pull θ.symm V ≤ L' := pull_le_L _
    have hUV' : U' ≤ pull θ.symm V := fun x hx =>
      mem_pull_symm.2 ⟨h.U_le_L hx, hUV ((pullE_mem_pull (h.U_le_L hx)).2 hx)⟩
    have hV'2 : IsPGroup 2 (pull θ.symm V) := hV2.of_equiv (pullEquiv (θ := θ.symm) hVL).symm
    have e := h.U_max _ hV'L hV'2 hUV'
    calc V = pull θ (pull θ.symm V) := (pull_symm_pull hVL).symm
      _ = pull θ U' := by rw [e]
  cent_Q := by
    intro l hl hc
    refine mem_pull.2 ⟨hl, h.cent_Q _ (θ ⟨l, hl⟩).2 fun q hq => ?_⟩
    have hqL := h.Q_le_L hq
    have e := theta_comm (θ := θ) hl (pullE_mem_L hqL) (hc _ ((pullE_mem_pull hqL).2 hq))
    rwa [theta_pullE] at e

end LinkFacts


@[expose] def AutCent (L Q : Subgroup G) : Prop :=
  ∀ α : MulAut L, (∀ x : L, (x : G) ∈ Q → α x = x) →
    ∃ q₀ ∈ Q, ∀ x : L, (α x : G) = q₀ * x * q₀⁻¹

namespace AutCent

variable {L Q : Subgroup G}

theorem transport {X : Type*} [Group X] {L' Q' : Subgroup X} (h : AutCent L' Q') (hQ : Q' ≤ L')
    (θ : L ≃* L') : AutCent L (pull θ Q') := by
  intro α hα
  set α' : MulAut L' := (θ.symm.trans α).trans θ
  have hα' : ∀ x' : L', (x' : X) ∈ Q' → α' x' = x' := by
    intro x' hx'
    have h1 : ((θ.symm x' : L) : G) ∈ pull θ Q' := by
      have := (pullE_mem_pull (θ := θ) (H' := Q') x'.2).2 hx'
      simpa [pullE] using this
    simp only [α', MulEquiv.trans_apply]
    rw [hα _ h1, MulEquiv.apply_symm_apply]
  obtain ⟨q₀', hq₀', hconj⟩ := h α' hα'
  refine ⟨pullE θ q₀' (hQ hq₀'), (pullE_mem_pull _).2 hq₀', fun x => ?_⟩
  have e1 : α x = θ.symm (α' (θ x)) := by simp [α']
  have e2 : α' (θ x) = ⟨q₀', hQ hq₀'⟩ * θ x * (⟨q₀', hQ hq₀'⟩ : L')⁻¹ := by
    apply Subtype.ext
    rw [hconj]
    rfl
  rw [e1, e2, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl

theorem conj_eq (h : AutCent L Q) {g : G} (hg : g ∈ normalizer (L : Set G))
    (hgQ : ∀ q ∈ Q, g * q = q * g) : ∃ q₀ ∈ Q, ∀ x ∈ L, g * x * g⁻¹ = q₀ * x * q₀⁻¹ := by
  obtain ⟨q₀, hq₀, hconj⟩ := h (L.normalizerMonoidHom ⟨g, hg⟩) fun x hx => by
    apply Subtype.ext
    change g * x * g⁻¹ = x
    rw [hgQ _ hx, mul_inv_cancel_right]
  exact ⟨q₀, hq₀, fun x hx => hconj ⟨x, hx⟩⟩

theorem centralizer_le (h : AutCent L Q) (hQL : Q ≤ L) {t : G}
    (hLt : L ≤ centralizer ({t} : Set G)) (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hCL : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) ≤ Q ⊔ zpowers t := by
  rintro g ⟨hgt, hgQ⟩
  obtain ⟨q₀, hq₀, hconj⟩ := h.conj_eq (hN hgt) fun q hq => (mem_centralizer_iff.1 hgQ q hq).symm
  have hc : q₀⁻¹ * g ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun x hx => ?_,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLt (hQL hq₀))) hgt⟩
    have := hconj x hx
    calc x * (q₀⁻¹ * g) = q₀⁻¹ * (q₀ * x * q₀⁻¹) * g := by group
      _ = q₀⁻¹ * (g * x * g⁻¹) * g := by rw [this]
      _ = q₀⁻¹ * g * x := by group
  rw [hCL] at hc
  have : g = q₀ * (q₀⁻¹ * g) := by group
  rw [this]
  exact mul_mem (mem_sup_left hq₀) (mem_sup_right hc)

end AutCent

end CFSG.EvenSmallLie.OmegaEight.Stage1
