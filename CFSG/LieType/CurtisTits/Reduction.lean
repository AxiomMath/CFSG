module

public import CFSG.LieType.CurtisTits.Amalgam
public import CFSG.LieType.CurtisTits.RootData
public import TauCeti.GroupTheory.Coxeter.Matsumoto

public section

namespace CFSG.LieType.CurtisTits

open CoxeterSystem

universe u w

variable {I : Type*}

section Levi

variable [DecidableEq I] {K : Type*} [Group K] (X : (I → ℤ) → Subgroup K)

@[expose] def rankOne (i : I) : Subgroup K := X (Pi.single i 1) ⊔ X (-Pi.single i 1)

@[expose] def levi (J : Finset I) : Subgroup K := ⨆ j ∈ J, rankOne X j

abbrev leviAmalgam : {J : Finset I // J.card ≤ 2} → Subgroup K := fun J => levi X J.1

theorem rankOne_le_levi {J : Finset I} {j : I} (hj : j ∈ J) : rankOne X j ≤ levi X J :=
  le_iSup₂_of_le (f := fun j (_ : j ∈ J) => rankOne X j) j hj le_rfl

theorem levi_mono {J J' : Finset I} (h : J ⊆ J') : levi X J ≤ levi X J' :=
  iSup₂_le fun _ hj => rankOne_le_levi X (h hj)

theorem levi_singleton (i : I) : levi X {i} = rankOne X i := by
  simp [levi]

end Levi

section RootGroups

variable [DecidableEq I] {M : CoxeterMatrix I} {W : Type*} [Group W] (cs : CoxeterSystem M W)
  (ρ : W →* Module.End ℤ (I → ℤ)) (Φ : Set (I → ℤ)) {K : Type u} [Group K]

structure IsCTGroupDatum (X : (I → ℤ) → Subgroup K) (n : I → K) (H : I → Subgroup K) : Prop where
  n_mem : ∀ i, n i ∈ rankOne X i
  conj_mem : ∀ i, ∀ γ ∈ Φ, ∀ x ∈ X γ, n i * x * (n i)⁻¹ ∈ X (ρ (cs.simple i) γ)
  braid : ∀ i j, ((braidWord M i j).map n).prod = ((braidWord M j i).map n).prod
  H_le : ∀ i, H i ≤ rankOne X i
  sq_mem : ∀ i, n i ^ 2 ∈ H i
  H_conj_mem : ∀ k, ∀ γ ∈ Φ, ∀ h ∈ H k, ∀ x ∈ X γ, h * x * h⁻¹ ∈ X γ
  conj_H_mem : ∀ j k, ∀ h ∈ H k, n j * h * (n j)⁻¹ ∈ H j ⊔ H k
  le_rankOne : ∀ i, ∀ γ ∈ Φ, (∀ k, k ≠ i → γ k = 0) → X γ ≤ rankOne X i
  iSup_eq_top : ⨆ γ ∈ Φ, X γ = ⊤

@[expose] def RelationsHold (X : (I → ℤ) → Subgroup K) (S : Set (I → ℤ)) {G : Type*} [Group G]
    (ψ : ∀ γ, X γ → G) : Prop :=
  ∀ l : List (Σ γ : I → ℤ, X γ), (∀ p ∈ l, p.1 ∈ S) →
    (l.map fun p => (p.2 : K)).prod = 1 → (l.map fun p => ψ p.1 p.2).prod = 1

@[expose] def IsPresentedBy (X : (I → ℤ) → Subgroup K) (rels : Set (Set (I → ℤ))) : Prop :=
  ∀ (G : Type w) [Group G] (ψ : ∀ γ, X γ → G), (∀ S ∈ rels, RelationsHold X S ψ) →
    ∃ φ : K →* G, ∀ γ ∈ Φ, ∀ x : X γ, φ x = ψ γ x

end RootGroups

section PositiveLift

variable {M : CoxeterMatrix I} {W : Type*} [Group W] (cs : CoxeterSystem M W)
  {G : Type*} [Group G] (f : I → G)
  (hf : ∀ i j, ((braidWord M i j).map f).prod = ((braidWord M j i).map f).prod)

local prefix:100 "ℓ " => cs.length

noncomputable def posLift : W → G :=
  (TauCeti.existsUnique_reducedWordLift cs f hf).exists.choose

theorem posLift_wordProd {ω : List I} (hω : cs.IsReduced ω) :
    posLift cs f hf (cs.wordProd ω) = (ω.map f).prod :=
  (TauCeti.existsUnique_reducedWordLift cs f hf).exists.choose_spec ω hω

theorem posLift_one : posLift cs f hf 1 = 1 := by
  have h := posLift_wordProd cs f hf (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa using h

theorem posLift_mul {a b : W} (h : ℓ (a * b) = ℓ a + ℓ b) :
    posLift cs f hf (a * b) = posLift cs f hf a * posLift cs f hf b := by
  obtain ⟨ωa, hωa, rfl⟩ := cs.exists_isReduced a
  obtain ⟨ωb, hωb, rfl⟩ := cs.exists_isReduced b
  have hred : cs.IsReduced (ωa ++ ωb) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, h, hωa.eq, hωb.eq, List.length_append]
  rw [← cs.wordProd_append, posLift_wordProd cs f hf hred, posLift_wordProd cs f hf hωa,
    posLift_wordProd cs f hf hωb, List.map_append, List.prod_append]

theorem posLift_simple_mul {w : W} {k : I} (h : ¬ cs.IsLeftDescent w k) :
    posLift cs f hf (cs.simple k * w) = f k * posLift cs f hf w := by
  have hlen : ℓ (cs.simple k * w) = ℓ (cs.simple k) + ℓ w := by
    rw [cs.not_isLeftDescent_iff.mp h, cs.length_simple, add_comm]
  rw [posLift_mul cs f hf hlen]
  congr 1
  have h1 := posLift_wordProd cs f hf (ω := [k]) (by
    rw [CoxeterSystem.IsReduced, cs.wordProd_singleton, cs.length_simple]; rfl)
  simpa using h1

theorem posLift_mem (S : Subgroup G) (hS : ∀ i, f i ∈ S) (w : W) : posLift cs f hf w ∈ S := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [posLift_wordProd cs f hf hω]
  exact S.list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact hS i

theorem map_posLift {G' : Type*} [Group G'] (g : G →* G')
    (hf' : ∀ i j, ((braidWord M i j).map (g ∘ f)).prod = ((braidWord M j i).map (g ∘ f)).prod)
    (w : W) : g (posLift cs f hf w) = posLift cs (g ∘ f) hf' w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [posLift_wordProd cs f hf hω, posLift_wordProd cs _ hf' hω, map_list_prod, List.map_map]

end PositiveLift

section Generic

variable {K : Type*} [Group K]

theorem conj_mem_sup {A B A' B' : Subgroup K} (c : K) (hA : ∀ x ∈ A, c * x * c⁻¹ ∈ A')
    (hB : ∀ x ∈ B, c * x * c⁻¹ ∈ B') : ∀ x ∈ A ⊔ B, c * x * c⁻¹ ∈ A' ⊔ B' := by
  intro x hx
  have hle : A ⊔ B ≤ (A' ⊔ B').comap (MulAut.conj c).toMonoidHom :=
    sup_le (fun y hy => Subgroup.mem_sup_left (hA y hy))
      (fun y hy => Subgroup.mem_sup_right (hB y hy))
  exact hle hx

theorem mem_of_mem_alternatingWord {I : Type*} {i j l : I} {m : ℕ}
    (h : l ∈ alternatingWord i j m) : l = i ∨ l = j := by
  induction m generalizing i j with
  | zero => simp [alternatingWord] at h
  | succ m ih =>
    rw [alternatingWord_succ, List.concat_eq_append, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact (ih h).symm
    · exact Or.inr h

end Generic

section Family

variable [DecidableEq I] {M : CoxeterMatrix I} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {ρ : W →* Module.End ℤ (I → ℤ)} {Φ : Set (I → ℤ)} {K : Type u} [Group K]
  {X : (I → ℤ) → Subgroup K} {n : I → K} {H : I → Subgroup K}
  {G : Type*} [Group G] (φ : ∀ J : {J : Finset I // J.card ≤ 2}, levi X J.1 →* G)

local prefix:100 "ℓ " => cs.length

open _root_.Classical in
private noncomputable def fam (J : Finset I) (x : K) : G :=
  if h : J.card ≤ 2 ∧ x ∈ levi X J then φ ⟨J, h.1⟩ ⟨x, h.2⟩ else 1

private theorem fam_of_mem {J : Finset I} (hJ : J.card ≤ 2) {x : K} (hx : x ∈ levi X J) :
    fam φ J x = φ ⟨J, hJ⟩ ⟨x, hx⟩ := by
  rw [fam]
  split_ifs with h
  · rfl
  · exact absurd ⟨hJ, hx⟩ h

private theorem fam_mul {J : Finset I} (hJ : J.card ≤ 2) {x y : K} (hx : x ∈ levi X J)
    (hy : y ∈ levi X J) : fam φ J (x * y) = fam φ J x * fam φ J y := by
  rw [fam_of_mem φ hJ hx, fam_of_mem φ hJ hy, fam_of_mem φ hJ (mul_mem hx hy), ← map_mul]
  rfl

private theorem fam_inv {J : Finset I} (hJ : J.card ≤ 2) {x : K} (hx : x ∈ levi X J) :
    fam φ J x⁻¹ = (fam φ J x)⁻¹ := by
  rw [fam_of_mem φ hJ hx, fam_of_mem φ hJ (inv_mem hx), ← map_inv]
  rfl

private theorem fam_one {J : Finset I} (hJ : J.card ≤ 2) : fam φ J (1 : K) = 1 := by
  rw [fam_of_mem φ hJ (one_mem _)]
  exact map_one (φ ⟨J, hJ⟩)

private theorem fam_conj {J : Finset I} (hJ : J.card ≤ 2) {x y : K} (hx : x ∈ levi X J)
    (hy : y ∈ levi X J) :
    fam φ J (x * y * x⁻¹) = fam φ J x * fam φ J y * (fam φ J x)⁻¹ := by
  rw [fam_mul φ hJ (mul_mem hx hy) (inv_mem hx), fam_mul φ hJ hx hy, fam_inv φ hJ hx]

private theorem fam_list_prod {J : Finset I} (hJ : J.card ≤ 2) :
    ∀ l : List K, (∀ x ∈ l, x ∈ levi X J) → fam φ J l.prod = (l.map (fam φ J)).prod
  | [], _ => by simp [fam_one φ hJ]
  | a :: l, h => by
    have ha : a ∈ levi X J := h a (by simp)
    have hl : ∀ x ∈ l, x ∈ levi X J := fun x hx => h x (by simp [hx])
    rw [List.prod_cons, List.map_cons, List.prod_cons, fam_mul φ hJ ha (list_prod_mem hl),
      fam_list_prod hJ l hl]

variable {φ}

private theorem fam_mono (hφ : IsCompatible (leviAmalgam X) φ) {J J' : Finset I}
    (hJ' : J'.card ≤ 2) (h : J ⊆ J') {x : K} (hx : x ∈ levi X J) : fam φ J x = fam φ J' x := by
  have hJ : J.card ≤ 2 := (Finset.card_le_card h).trans hJ'
  rw [fam_of_mem φ hJ hx, fam_of_mem φ hJ' (levi_mono X h hx)]
  exact hφ ⟨J, hJ⟩ ⟨J', hJ'⟩ h ⟨x, hx⟩ ⟨x, levi_mono X h hx⟩ rfl

private theorem mem_levi_singleton {i : I} {y : K} (hy : y ∈ rankOne X i) : y ∈ levi X {i} := by
  rwa [levi_singleton]

private theorem fam_singleton_eq (hφ : IsCompatible (leviAmalgam X) φ) {J : Finset I}
    (hJ : J.card ≤ 2) {i : I} (hi : i ∈ J) {y : K} (hy : y ∈ rankOne X i) :
    fam φ {i} y = fam φ J y :=
  fam_mono hφ hJ (Finset.singleton_subset_iff.mpr hi) (mem_levi_singleton hy)

variable (φ n) in
private noncomputable def nh (i : I) : G := fam φ {i} (n i)

private theorem prod_map_nh (hφ : IsCompatible (leviAmalgam X) φ)
    (hn : ∀ i, n i ∈ rankOne X i) {J : Finset I} (hJ : J.card ≤ 2) :
    ∀ ω : List I, (∀ i ∈ ω, i ∈ J) → (ω.map (nh n φ)).prod = fam φ J (ω.map n).prod
  | [], _ => by simp [fam_one φ hJ]
  | a :: ω, hω => by
    have ha : a ∈ J := hω a (by simp)
    have hωJ : ∀ i ∈ ω, i ∈ J := fun i hi => hω i (by simp [hi])
    have hrest : (ω.map n).prod ∈ levi X J := list_prod_mem fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact rankOne_le_levi X (hωJ b hb) (hn b)
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      fam_mul φ hJ (rankOne_le_levi X ha (hn a)) hrest, prod_map_nh hφ hn hJ ω hωJ, nh,
      fam_singleton_eq hφ hJ ha (hn a)]

private theorem braid_nh (hφ : IsCompatible (leviAmalgam X) φ)
    (hK : IsCTGroupDatum cs ρ Φ X n H) (i j : I) :
    ((braidWord M i j).map (nh n φ)).prod = ((braidWord M j i).map (nh n φ)).prod := by
  have hJ : ({i, j} : Finset I).card ≤ 2 := Finset.card_le_two
  have h1 : ∀ l ∈ braidWord M i j, l ∈ ({i, j} : Finset I) := fun l hl => by
    rcases mem_of_mem_alternatingWord hl with rfl | rfl <;> simp
  have h2 : ∀ l ∈ braidWord M j i, l ∈ ({i, j} : Finset I) := fun l hl => by
    rcases mem_of_mem_alternatingWord hl with rfl | rfl <;> simp
  rw [prod_map_nh hφ hK.n_mem hJ _ h1, prod_map_nh hφ hK.n_mem hJ _ h2, hK.braid]

private noncomputable def nt (hφ : IsCompatible (leviAmalgam X) φ)
    (hK : IsCTGroupDatum cs ρ Φ X n H) : W → G :=
  posLift cs (nh n φ) (braid_nh hφ hK)

private noncomputable def nK (hK : IsCTGroupDatum cs ρ Φ X n H) : W → K :=
  posLift cs n hK.braid

variable (hφ : IsCompatible (leviAmalgam X) φ) (hK : IsCTGroupDatum cs ρ Φ X n H)

private theorem nt_one : nt hφ hK 1 = 1 := posLift_one ..

private theorem nK_one : nK hK 1 = 1 := posLift_one ..

private theorem nt_mul {a b : W} (h : ℓ (a * b) = ℓ a + ℓ b) :
    nt hφ hK (a * b) = nt hφ hK a * nt hφ hK b :=
  posLift_mul cs _ _ h

private theorem nK_mul {a b : W} (h : ℓ (a * b) = ℓ a + ℓ b) :
    nK hK (a * b) = nK hK a * nK hK b :=
  posLift_mul cs _ _ h

private theorem nt_simple_mul {w : W} {k : I} (h : ¬ cs.IsLeftDescent w k) :
    nt hφ hK (cs.simple k * w) = nh n φ k * nt hφ hK w :=
  posLift_simple_mul cs _ _ h

private theorem nK_mem_levi {J : Finset I} {x : W} (hx : x ∈ cs.parabolic (J : Set I)) :
    nK hK x ∈ levi X J := by
  obtain ⟨ω, hω, hωJ, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hx
  rw [nK, posLift_wordProd _ _ _ hω]
  exact list_prod_mem fun y hy => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact rankOne_le_levi X (by exact_mod_cast hωJ b hb) (hK.n_mem b)

private theorem nt_parabolic {J : Finset I} (hJ : J.card ≤ 2) {x : W}
    (hx : x ∈ cs.parabolic (J : Set I)) : nt hφ hK x = fam φ J (nK hK x) := by
  obtain ⟨ω, hω, hωJ, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hx
  rw [nt, nK, posLift_wordProd _ _ _ hω, posLift_wordProd _ _ _ hω]
  exact prod_map_nh hφ hK.n_mem hJ ω fun i hi => by exact_mod_cast hωJ i hi

private theorem π_nt (π : G →* K) (hπ : ∀ J x, π (φ J x) = x) (w : W) :
    π (nt hφ hK w) = nK hK w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [nt, nK, posLift_wordProd _ _ _ hω, posLift_wordProd _ _ _ hω, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, nh]
  rw [fam_of_mem φ (by simp) (mem_levi_singleton (hK.n_mem i)), hπ]

omit [DecidableEq I] in
private theorem rho_one_apply (v : I → ℤ) : ρ 1 v = v := by
  rw [map_one]; rfl

omit [DecidableEq I] in
private theorem rho_mul_apply (a b : W) (v : I → ℤ) : ρ (a * b) v = ρ a (ρ b v) := by
  rw [map_mul]; rfl

private theorem conj_inv_mem (hΦ : IsCTRootSystem cs ρ Φ) (hK : IsCTGroupDatum cs ρ Φ X n H)
    (i : I) : ∀ γ ∈ Φ, ∀ x ∈ X γ, (n i)⁻¹ * x * n i ∈ X (ρ (cs.simple i) γ) := by
  intro γ hγ x hx
  have hγ' : ρ (cs.simple i) γ ∈ Φ := hΦ.smul_mem _ γ hγ
  have h1 := hK.conj_mem i γ hγ x hx
  have h2 := hK.H_conj_mem i _ hγ' _ (inv_mem (hK.sq_mem i)) _ h1
  have : (n i)⁻¹ * x * n i = (n i ^ 2)⁻¹ * (n i * x * (n i)⁻¹) * ((n i ^ 2)⁻¹)⁻¹ := by group
  rw [this]
  exact h2


private theorem conj_prod_mem (hΦ : IsCTRootSystem cs ρ Φ) (hK : IsCTGroupDatum cs ρ Φ X n H) :
    ∀ (ω : List I), ∀ γ ∈ Φ, ∀ x ∈ X γ,
      (ω.map n).prod * x * ((ω.map n).prod)⁻¹ ∈ X (ρ (cs.wordProd ω) γ)
  | [], γ, _, x, hx => by simpa [rho_one_apply] using hx
  | a :: ω, γ, hγ, x, hx => by
    have h := conj_prod_mem hΦ hK ω γ hγ x hx
    have h' := hK.conj_mem a _ (hΦ.smul_mem _ γ hγ) _ h
    rw [cs.wordProd_cons, rho_mul_apply]
    simpa [List.map_cons, List.prod_cons, mul_assoc] using h'

private theorem conj_prod_inv_mem (hΦ : IsCTRootSystem cs ρ Φ)
    (hK : IsCTGroupDatum cs ρ Φ X n H) :
    ∀ (ω : List I), ∀ γ ∈ Φ, ∀ x ∈ X γ,
      ((ω.map n).prod)⁻¹ * x * (ω.map n).prod ∈ X (ρ (cs.wordProd ω)⁻¹ γ)
  | [], γ, _, x, hx => by simpa [rho_one_apply] using hx
  | a :: ω, γ, hγ, x, hx => by
    have h := conj_inv_mem hΦ hK a γ hγ x hx
    have h' := conj_prod_inv_mem hΦ hK ω _ (hΦ.smul_mem _ γ hγ) _ h
    rw [cs.wordProd_cons, mul_inv_rev, cs.inv_simple, rho_mul_apply]
    simpa [List.map_cons, List.prod_cons, mul_assoc] using h'

private theorem conj_nK_mem (hΦ : IsCTRootSystem cs ρ Φ) (w : W) {γ : I → ℤ} (hγ : γ ∈ Φ)
    {x : K} (hx : x ∈ X γ) : nK hK w * x * (nK hK w)⁻¹ ∈ X (ρ w γ) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [nK, posLift_wordProd _ _ _ hω]
  exact conj_prod_mem hΦ hK ω γ hγ x hx

private theorem conj_nK_inv_mem (hΦ : IsCTRootSystem cs ρ Φ) (w : W) {γ : I → ℤ}
    (hγ : γ ∈ Φ) {x : K} (hx : x ∈ X γ) : (nK hK w)⁻¹ * x * nK hK w ∈ X (ρ w⁻¹ γ) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [nK, posLift_wordProd _ _ _ hω]
  exact conj_prod_inv_mem hΦ hK ω γ hγ x hx

private theorem conj_nK_rankOne (hΦ : IsCTRootSystem cs ρ Φ) {w : W} {i j : I}
    (hij : ρ w (Pi.single i 1) = Pi.single j 1) {y : K} (hy : y ∈ rankOne X i) :
    nK hK w * y * (nK hK w)⁻¹ ∈ rankOne X j := by
  have hneg : ρ w (-Pi.single i 1) = -Pi.single j 1 := by rw [map_neg, hij]
  have hmem : -Pi.single i 1 ∈ Φ := by
    have := hΦ.smul_mem (cs.simple i) _ (hΦ.single_mem i)
    rwa [hΦ.simple_single] at this
  refine conj_mem_sup _ (fun x hx => ?_) (fun x hx => ?_) y hy
  · have := conj_nK_mem hK hΦ w (hΦ.single_mem i) hx
    rwa [hij] at this
  · have := conj_nK_mem hK hΦ w hmem hx
    rwa [hneg] at this

private theorem parabolic_support (hΦ : IsCTRootSystem cs ρ Φ) {J : Set I} {z : W}
    (hz : z ∈ cs.parabolic J) {γ : I → ℤ} (hγ : ∀ k ∉ J, γ k = 0) : ∀ k ∉ J, ρ z γ k = 0 := by
  obtain ⟨ω, hωJ, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hz
  clear hz
  induction ω with
  | nil => simpa [rho_one_apply] using hγ
  | cons a ω ih =>
    intro k hk
    rw [cs.wordProd_cons, rho_mul_apply,
      hΦ.simple_apply_of_ne a _ k (fun h => hk (h ▸ hωJ a (by simp)))]
    exact ih (fun i hi => hωJ i (by simp [hi])) k hk

include hK in
private theorem X_le_levi (hΦ : IsCTRootSystem cs ρ Φ) {J : Finset I} {γ : I → ℤ}
    (hγ : γ ∈ Φ) (hsupp : ∀ k ∉ J, γ k = 0) : X γ ≤ levi X J := by
  intro x hx
  obtain ⟨w, i, c, hc, rfl⟩ := hΦ.exists_eq γ hγ
  have hsupp' : ∀ k ∉ (J : Set I), ρ w (Pi.single i 1) k = 0 := by
    intro k hk
    have := hsupp k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left hc
  obtain ⟨z, hz, m, hm, hzm⟩ := hΦ.exists_parabolic (J : Set I) w i hsupp'
  have hzγ : ρ z (c • ρ w (Pi.single i 1)) = c • Pi.single m 1 := by rw [map_zsmul, hzm]
  have hcm : c • Pi.single m 1 ∈ Φ := hzγ ▸ hΦ.smul_mem z _ hγ
  have hx' := conj_nK_mem hK hΦ z hγ hx
  rw [hzγ] at hx'
  have hrank : X (c • Pi.single m 1) ≤ rankOne X m := hK.le_rankOne m _ hcm fun k hk => by
    simp [Pi.single_eq_of_ne hk]
  have hmem := rankOne_le_levi X (by exact_mod_cast hm) (hrank hx')
  have hnz := nK_mem_levi hK hz
  have : x = (nK hK z)⁻¹ * (nK hK z * x * (nK hK z)⁻¹) * nK hK z := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hnz) hmem) hnz

variable (φ H) in
private noncomputable def Hhat : Subgroup G :=
  Subgroup.closure (⋃ k, fam φ {k} '' (H k : Set K))

private theorem fam_mem_Hhat {k : I} {h : K} (hh : h ∈ H k) : fam φ {k} h ∈ Hhat H φ :=
  Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨k, h, hh, rfl⟩)

include hφ hK in
private theorem fam_pair_mem_Hhat (j k : I) {t : K} (ht : t ∈ H j ⊔ H k) :
    fam φ {j, k} t ∈ Hhat H φ := by
  have hJ : ({j, k} : Finset I).card ≤ 2 := Finset.card_le_two
  have hle : H j ⊔ H k ≤ levi X {j, k} :=
    sup_le ((hK.H_le j).trans (rankOne_le_levi X (by simp)))
      ((hK.H_le k).trans (rankOne_le_levi X (by simp)))
  rw [Subgroup.sup_eq_closure] at ht hle
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    rcases ht with ht | ht
    · rw [← fam_singleton_eq hφ hJ (by simp) (hK.H_le j ht)]
      exact fam_mem_Hhat ht
    · rw [← fam_singleton_eq hφ hJ (by simp) (hK.H_le k ht)]
      exact fam_mem_Hhat ht
  | one => rw [fam_one φ hJ]; exact one_mem _
  | mul a b ha hb iha ihb =>
    rw [fam_mul φ hJ (hle ha) (hle hb)]
    exact mul_mem iha ihb
  | inv a ha iha =>
    rw [fam_inv φ hJ (hle ha)]
    exact inv_mem iha

include hφ hK in
private theorem nh_conj_mem_Hhat (j : I) {g : G} (hg : g ∈ Hhat H φ) :
    nh n φ j * g * (nh n φ j)⁻¹ ∈ Hhat H φ := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    obtain ⟨h, hh, rfl⟩ := hk
    have hJ : ({j, k} : Finset I).card ≤ 2 := Finset.card_le_two
    have hnj : n j ∈ levi X {j, k} := rankOne_le_levi X (by simp) (hK.n_mem j)
    have hhk : h ∈ levi X {j, k} := rankOne_le_levi X (by simp) (hK.H_le k hh)
    rw [nh, fam_singleton_eq hφ hJ (by simp) (hK.n_mem j),
      fam_singleton_eq hφ hJ (by simp) (hK.H_le k hh), ← fam_conj φ hJ hnj hhk]
    exact fam_pair_mem_Hhat hφ hK j k (hK.conj_H_mem j k h hh)
  | one => simp
  | mul a b _ _ iha ihb =>
    have : nh n φ j * (a * b) * (nh n φ j)⁻¹ =
        (nh n φ j * a * (nh n φ j)⁻¹) * (nh n φ j * b * (nh n φ j)⁻¹) := by group
    rw [this]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have : nh n φ j * a⁻¹ * (nh n φ j)⁻¹ = (nh n φ j * a * (nh n φ j)⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem iha

include hK in
private theorem nh_sq_mem_Hhat (j : I) : nh n φ j ^ 2 ∈ Hhat H φ := by
  have hJ : ({j} : Finset I).card ≤ 2 := by simp
  have hn : n j ∈ levi X {j} := mem_levi_singleton (hK.n_mem j)
  have : nh n φ j ^ 2 = fam φ {j} (n j ^ 2) := by rw [nh, pow_two, pow_two, fam_mul φ hJ hn hn]
  rw [this]
  exact fam_mem_Hhat (hK.sq_mem j)

include hφ hK in
private theorem nh_inv_conj_mem_Hhat (j : I) {g : G} (hg : g ∈ Hhat H φ) :
    (nh n φ j)⁻¹ * g * nh n φ j ∈ Hhat H φ := by
  have hsq := nh_sq_mem_Hhat (φ := φ) hK j
  have : (nh n φ j)⁻¹ * g * nh n φ j =
      (nh n φ j ^ 2)⁻¹ * (nh n φ j * g * (nh n φ j)⁻¹) * nh n φ j ^ 2 := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hsq) (nh_conj_mem_Hhat hφ hK j hg)) hsq

private theorem nt_conj_mem_Hhat (w : W) {g : G} (hg : g ∈ Hhat H φ) :
    nt hφ hK w * g * (nt hφ hK w)⁻¹ ∈ Hhat H φ := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [nt, posLift_wordProd _ _ _ hω]
  clear hω
  induction ω generalizing g with
  | nil => simpa using hg
  | cons a ω ih =>
    have : (List.map (nh n φ) (a :: ω)).prod * g * ((List.map (nh n φ) (a :: ω)).prod)⁻¹ =
        nh n φ a * ((List.map (nh n φ) ω).prod * g * ((List.map (nh n φ) ω).prod)⁻¹) *
          (nh n φ a)⁻¹ := by
      simp only [List.map_cons, List.prod_cons]; group
    rw [this]
    exact nh_conj_mem_Hhat hφ hK a (ih hg)

private theorem nh_mul_nt (k : I) (w : W) :
    ∃ g ∈ Hhat H φ, nh n φ k * nt hφ hK w = g * nt hφ hK (cs.simple k * w) := by
  by_cases h : cs.IsLeftDescent w k
  · have h' : ¬ cs.IsLeftDescent (cs.simple k * w) k :=
      cs.isLeftDescent_iff_not_isLeftDescent_mul.mp h
    have hw : w = cs.simple k * (cs.simple k * w) := by
      rw [cs.simple_mul_simple_cancel_left]
    refine ⟨nh n φ k ^ 2, nh_sq_mem_Hhat hK k, ?_⟩
    conv_lhs => rw [hw, nt_simple_mul hφ hK h']
    rw [pow_two, mul_assoc]
  · exact ⟨1, one_mem _, by rw [nt_simple_mul hφ hK h, one_mul]⟩

private theorem nt_mul_nt (u v : W) :
    ∃ g ∈ Hhat H φ, nt hφ hK u * nt hφ hK v = g * nt hφ hK (u * v) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced u
  induction ω with
  | nil => exact ⟨1, one_mem _, by simp [nt_one]⟩
  | cons a ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hdesc : ¬ cs.IsLeftDescent (cs.wordProd ω) a := by
      rw [cs.not_isLeftDescent_iff, ← cs.wordProd_cons, hω.eq, hω'.eq, List.length_cons]
    obtain ⟨g₁, hg₁, h₁⟩ := ih hω'
    obtain ⟨g₂, hg₂, h₂⟩ := nh_mul_nt hφ hK a (cs.wordProd ω * v)
    refine ⟨nh n φ a * g₁ * (nh n φ a)⁻¹ * g₂, mul_mem (nh_conj_mem_Hhat hφ hK a hg₁) hg₂, ?_⟩
    rw [cs.wordProd_cons, nt_simple_mul hφ hK hdesc, mul_assoc, h₁, mul_assoc]
    have : nh n φ a * (g₁ * nt hφ hK (cs.wordProd ω * v)) =
        nh n φ a * g₁ * (nh n φ a)⁻¹ * (nh n φ a * nt hφ hK (cs.wordProd ω * v)) := by group
    rw [this, h₂, mul_assoc (cs.simple a)]

private theorem neg_single_mem (hΦ : IsCTRootSystem cs ρ Φ) (j : I) :
    -Pi.single j 1 ∈ Φ := by
  have := hΦ.smul_mem (cs.simple j) _ (hΦ.single_mem j)
  rwa [hΦ.simple_single] at this

include hφ hK in
private theorem Hhat_conj (hΦ : IsCTRootSystem cs ρ Φ) (π : G →* K)
    (hπ : ∀ J x, π (φ J x) = x) {g : G} (hg : g ∈ Hhat H φ) (j : I) :
    (∀ y, y ∈ rankOne X j ↔ π g * y * (π g)⁻¹ ∈ rankOne X j) ∧
      ∀ y ∈ rankOne X j, g * fam φ {j} y * g⁻¹ = fam φ {j} (π g * y * (π g)⁻¹) := by
  have hpres : ∀ k, ∀ h ∈ H k, ∀ y ∈ rankOne X j, h * y * h⁻¹ ∈ rankOne X j :=
    fun k h hh => conj_mem_sup h (fun x hx => hK.H_conj_mem k _ (hΦ.single_mem j) h hh x hx)
      (fun x hx => hK.H_conj_mem k _ (neg_single_mem hΦ j) h hh x hx)
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    obtain ⟨h, hh, rfl⟩ := hk
    have hhk : h ∈ levi X {k} := mem_levi_singleton (hK.H_le k hh)
    have hπh : π (fam φ {k} h) = h := by rw [fam_of_mem φ (by simp) hhk, hπ]
    rw [hπh]
    refine ⟨fun y => ⟨fun hy => hpres k h hh y hy, fun hy => ?_⟩, fun y hy => ?_⟩
    · have := hpres k h⁻¹ (inv_mem hh) _ hy
      simpa [mul_assoc] using this
    · have hJ : ({j, k} : Finset I).card ≤ 2 := Finset.card_le_two
      have hhy := hpres k h hh y hy
      rw [fam_singleton_eq hφ hJ (by simp) hy, fam_singleton_eq hφ hJ (by simp) (hK.H_le k hh),
        fam_singleton_eq hφ hJ (by simp) hhy,
        fam_conj φ hJ (rankOne_le_levi X (by simp) (hK.H_le k hh))
          (rankOne_le_levi X (by simp) hy)]
  | one => simp
  | mul a b _ _ iha ihb =>
    obtain ⟨ha1, ha2⟩ := iha
    obtain ⟨hb1, hb2⟩ := ihb
    have e : ∀ y, π (a * b) * y * (π (a * b))⁻¹ = π a * (π b * y * (π b)⁻¹) * (π a)⁻¹ :=
      fun y => by rw [map_mul]; group
    refine ⟨fun y => by rw [e, hb1 y, ha1], fun y hy => ?_⟩
    have : a * b * fam φ {j} y * (a * b)⁻¹ = a * (b * fam φ {j} y * b⁻¹) * a⁻¹ := by group
    rw [this, hb2 y hy, ha2 _ ((hb1 y).mp hy), e]
  | inv a _ iha =>
    obtain ⟨ha1, ha2⟩ := iha
    have e : ∀ y, π a * ((π a)⁻¹ * y * π a) * (π a)⁻¹ = y := fun y => by group
    have h1 : ∀ y, y ∈ rankOne X j ↔ (π a)⁻¹ * y * π a ∈ rankOne X j := fun y => by
      rw [ha1 ((π a)⁻¹ * y * π a), e]
    refine ⟨fun y => by rw [map_inv, inv_inv]; exact h1 y, fun y hy => ?_⟩
    have hy' := (h1 y).mp hy
    have h2 := ha2 _ hy'
    rw [e] at h2
    rw [map_inv, inv_inv, ← h2]
    group

private theorem conj_nt_eq (hΦ : IsCTRootSystem cs ρ Φ) (N : ℕ) : ∀ (v : W), ℓ v = N →
    ∀ (i j : I), ρ v (Pi.single i 1) = Pi.single j 1 → ∀ y ∈ rankOne X i,
      nt hφ hK v * fam φ {i} y * (nt hφ hK v)⁻¹ = fam φ {j} (nK hK v * y * (nK hK v)⁻¹) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro v hvN i j hij y hy
  by_cases hv1 : v = 1
  · subst hv1
    have hij' : i = j := by
      rw [rho_one_apply] at hij
      by_contra hne
      have := congrFun hij i
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
      exact one_ne_zero this
    subst hij'
    simp [nt_one, nK_one]
  obtain ⟨k, hk⟩ := cs.exists_leftDescent_of_ne_one hv1
  have hinv : ρ v⁻¹ (Pi.single j 1) = Pi.single i 1 := by
    rw [← hij, ← rho_mul_apply, inv_mul_cancel, rho_one_apply]
  have hkj : k ≠ j := by
    rintro rfl
    exact hΦ.not_isLeftDescent v k (by rw [hinv]; exact Pi.single_nonneg.mpr zero_le_one) hk
  set J : Finset I := {j, k} with hJdef
  have hJ : J.card ≤ 2 := Finset.card_le_two
  obtain ⟨⟨x, v₀⟩, ⟨hx, hv₀, hvx⟩, -⟩ := cs.existsUnique_mem_parabolic_mul (J : Set I) v
  simp only at hx hv₀ hvx
  have hlen := cs.length_mul_of_forall_not_isLeftDescent hx hv₀
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [one_mul] at hvx
    exact hv₀ k (by simp [J]) (hvx ▸ hk)
  have hlt : ℓ v₀ < N := by
    have hxpos : 0 < ℓ x := Nat.pos_of_ne_zero fun h => hx1 (cs.length_eq_zero_iff.mp h)
    rw [← hvN, hvx, hlen]
    omega
  have hsupp : ∀ l ∉ (J : Set I), ρ v₀ (Pi.single i 1) l = 0 := by
    have h0 : ρ v₀ (Pi.single i 1) = ρ x⁻¹ (Pi.single j 1) := by
      rw [← hij, hvx, ← rho_mul_apply, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h0]
    refine parabolic_support hΦ (inv_mem hx) fun l hl => Pi.single_eq_of_ne (fun h => hl ?_) 1
    subst h
    simp [J]
  obtain ⟨m, hm, hv₀m⟩ := hΦ.eq_single (J : Set I) v₀ i hv₀ hsupp
  have hm' : m ∈ J := by exact_mod_cast hm
  have hxm : ρ x (Pi.single m 1) = Pi.single j 1 := by
    rw [← hv₀m, ← rho_mul_apply, ← hvx, hij]
  have ih' := ih (ℓ v₀) hlt v₀ rfl i m hv₀m y hy
  have hntx := nt_parabolic hφ hK hJ hx
  have hnKx := nK_mem_levi hK hx
  have hnt : nt hφ hK v = nt hφ hK x * nt hφ hK v₀ := by rw [hvx]; exact nt_mul hφ hK hlen
  have hnK : nK hK v = nK hK x * nK hK v₀ := by rw [hvx]; exact nK_mul hK hlen
  have hy' : nK hK v₀ * y * (nK hK v₀)⁻¹ ∈ rankOne X m := conj_nK_rankOne hK hΦ hv₀m hy
  have hy'' : nK hK x * (nK hK v₀ * y * (nK hK v₀)⁻¹) * (nK hK x)⁻¹ ∈ rankOne X j :=
    conj_nK_rankOne hK hΦ hxm hy'
  calc nt hφ hK v * fam φ {i} y * (nt hφ hK v)⁻¹
      = nt hφ hK x * (nt hφ hK v₀ * fam φ {i} y * (nt hφ hK v₀)⁻¹) * (nt hφ hK x)⁻¹ := by
        rw [hnt]; group
    _ = fam φ J (nK hK x) * fam φ J (nK hK v₀ * y * (nK hK v₀)⁻¹) *
          (fam φ J (nK hK x))⁻¹ := by
        rw [ih', hntx, fam_singleton_eq hφ hJ hm' hy']
    _ = fam φ J (nK hK x * (nK hK v₀ * y * (nK hK v₀)⁻¹) * (nK hK x)⁻¹) :=
        (fam_conj φ hJ hnKx (rankOne_le_levi X hm' hy')).symm
    _ = fam φ {j} (nK hK x * (nK hK v₀ * y * (nK hK v₀)⁻¹) * (nK hK x)⁻¹) :=
        (fam_singleton_eq hφ hJ (by simp [J]) hy'').symm
    _ = fam φ {j} (nK hK v * y * (nK hK v)⁻¹) := by
        rw [hnK]; congr 1; group

private theorem conj_Hhat_nt_eq (hΦ : IsCTRootSystem cs ρ Φ) (π : G →* K)
    (hπ : ∀ J x, π (φ J x) = x) {g : G} (hg : g ∈ Hhat H φ) {v : W} {i j : I}
    (hij : ρ v (Pi.single i 1) = Pi.single j 1) {y : K} (hy : y ∈ rankOne X i) :
    π (g * nt hφ hK v) * y * (π (g * nt hφ hK v))⁻¹ ∈ rankOne X j ∧
      g * nt hφ hK v * fam φ {i} y * (g * nt hφ hK v)⁻¹ =
        fam φ {j} (π (g * nt hφ hK v) * y * (π (g * nt hφ hK v))⁻¹) := by
  have h1 := conj_nt_eq hφ hK hΦ _ v rfl i j hij y hy
  have hy' := conj_nK_rankOne hK hΦ hij hy
  have hc := Hhat_conj hφ hK hΦ π hπ hg j
  have e : π (g * nt hφ hK v) * y * (π (g * nt hφ hK v))⁻¹ =
      π g * (nK hK v * y * (nK hK v)⁻¹) * (π g)⁻¹ := by
    rw [map_mul, π_nt hφ hK π hπ]; group
  refine ⟨by rw [e]; exact (hc.1 _).mp hy', ?_⟩
  rw [e, ← hc.2 _ hy', ← h1]
  group

private theorem conj_Hhat_nt_eq_levi (hΦ : IsCTRootSystem cs ρ Φ) (π : G →* K)
    (hπ : ∀ J x, π (φ J x) = x) {g : G} (hg : g ∈ Hhat H φ) {v : W} {i : I} {J : Finset I}
    (hJ : J.card ≤ 2) (hsupp : ∀ k ∉ J, ρ v (Pi.single i 1) k = 0) {y : K}
    (hy : y ∈ rankOne X i) :
    π (g * nt hφ hK v) * y * (π (g * nt hφ hK v))⁻¹ ∈ levi X J ∧
      g * nt hφ hK v * fam φ {i} y * (g * nt hφ hK v)⁻¹ =
        fam φ J (π (g * nt hφ hK v) * y * (π (g * nt hφ hK v))⁻¹) := by
  obtain ⟨z, hz, m, hm, hzm⟩ :=
    hΦ.exists_parabolic (J : Set I) v i fun k hk => hsupp k (by exact_mod_cast hk)
  have hm' : m ∈ J := by exact_mod_cast hm
  obtain ⟨g₂, hg₂, h₂⟩ := nt_mul_nt hφ hK z v
  have hg' : nt hφ hK z * g * (nt hφ hK z)⁻¹ * g₂ ∈ Hhat H φ :=
    mul_mem (nt_conj_mem_Hhat hφ hK z hg) hg₂
  have heq : nt hφ hK z * (g * nt hφ hK v) =
      (nt hφ hK z * g * (nt hφ hK z)⁻¹ * g₂) * nt hφ hK (z * v) := by
    rw [mul_assoc _ g₂, ← h₂]; group
  have hzv : ρ (z * v) (Pi.single i 1) = Pi.single m 1 := by rw [rho_mul_apply, hzm]
  obtain ⟨hc, hk⟩ := conj_Hhat_nt_eq hφ hK hΦ π hπ hg' hzv hy
  rw [← heq] at hc hk
  set c := π (g * nt hφ hK v) * y * (π (g * nt hφ hK v))⁻¹ with hcdef
  have hπz : π (nt hφ hK z * (g * nt hφ hK v)) * y * (π (nt hφ hK z * (g * nt hφ hK v)))⁻¹ =
      nK hK z * c * (nK hK z)⁻¹ := by
    rw [map_mul, π_nt hφ hK π hπ, hcdef]; group
  rw [hπz] at hc hk
  have hnz := nK_mem_levi hK hz
  have hcJ : nK hK z * c * (nK hK z)⁻¹ ∈ levi X J := rankOne_le_levi X hm' hc
  have hcmem : c ∈ levi X J := by
    have : c = (nK hK z)⁻¹ * (nK hK z * c * (nK hK z)⁻¹) * nK hK z := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hnz) hcJ) hnz
  refine ⟨hcmem, ?_⟩
  have hntz := nt_parabolic hφ hK hJ hz
  have hk' : nt hφ hK z * (g * nt hφ hK v * fam φ {i} y * (g * nt hφ hK v)⁻¹) *
      (nt hφ hK z)⁻¹ = fam φ J (nK hK z) * fam φ J c * (fam φ J (nK hK z))⁻¹ := by
    rw [← fam_conj φ hJ hnz hcmem, ← fam_singleton_eq hφ hJ hm' hc, ← hk]
    group
  rw [hntz] at hk'
  exact mul_left_cancel (mul_right_cancel hk')

private theorem rootMap_eq (hΦ : IsCTRootSystem cs ρ Φ) (π : G →* K)
    (hπ : ∀ J x, π (φ J x) = x) {γ : I → ℤ} (hγ : γ ∈ Φ) {w : W} {i : I} {c : ℤ} (hc : c ≠ 0)
    (hγeq : γ = c • ρ w (Pi.single i 1)) (u : W) {J : Finset I} (hJ : J.card ≤ 2)
    (hsupp : ∀ k ∉ J, ρ u γ k = 0) {x : K} (hx : x ∈ X γ) :
    nt hφ hK w * fam φ {i} ((nK hK w)⁻¹ * x * nK hK w) * (nt hφ hK w)⁻¹ =
      (nt hφ hK u)⁻¹ * fam φ J (nK hK u * x * (nK hK u)⁻¹) * nt hφ hK u := by
  have hwγ : ρ w⁻¹ γ = c • Pi.single i 1 := by
    rw [hγeq, map_zsmul, ← rho_mul_apply, inv_mul_cancel, rho_one_apply]
  have hy := conj_nK_inv_mem hK hΦ w hγ hx
  rw [hwγ] at hy
  have hci : c • Pi.single i 1 ∈ Φ := hwγ ▸ hΦ.smul_mem w⁻¹ γ hγ
  have hy' : (nK hK w)⁻¹ * x * nK hK w ∈ rankOne X i :=
    hK.le_rankOne i _ hci (fun k hk => by simp [Pi.single_eq_of_ne hk]) hy
  have hsupp' : ∀ k ∉ J, ρ (u * w) (Pi.single i 1) k = 0 := by
    intro k hk
    have h := hsupp k hk
    rw [hγeq, map_zsmul, ← rho_mul_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left hc
  obtain ⟨g, hg, hgeq⟩ := nt_mul_nt hφ hK u w
  obtain ⟨-, h⟩ := conj_Hhat_nt_eq_levi hφ hK hΦ π hπ hg hJ hsupp' hy'
  rw [← hgeq] at h
  have hπuw : π (nt hφ hK u * nt hφ hK w) * ((nK hK w)⁻¹ * x * nK hK w) *
      (π (nt hφ hK u * nt hφ hK w))⁻¹ = nK hK u * x * (nK hK u)⁻¹ := by
    rw [map_mul, π_nt hφ hK π hπ, π_nt hφ hK π hπ]; group
  rw [hπuw] at h
  rw [← h]
  group

variable (hΦ : IsCTRootSystem cs ρ Φ)

open _root_.Classical in
private noncomputable def psi (γ : I → ℤ) (x : X γ) : G :=
  if hγ : γ ∈ Φ then
    nt hφ hK (hΦ.exists_eq γ hγ).choose * fam φ {(hΦ.exists_eq γ hγ).choose_spec.choose}
      ((nK hK (hΦ.exists_eq γ hγ).choose)⁻¹ * x * nK hK (hΦ.exists_eq γ hγ).choose) *
      (nt hφ hK (hΦ.exists_eq γ hγ).choose)⁻¹
  else 1

private theorem psi_eq (π : G →* K) (hπ : ∀ J x, π (φ J x) = x) {γ : I → ℤ} (hγ : γ ∈ Φ)
    (u : W) {J : Finset I} (hJ : J.card ≤ 2) (hsupp : ∀ k ∉ J, ρ u γ k = 0) (x : X γ) :
    psi hφ hK hΦ γ x = (nt hφ hK u)⁻¹ * fam φ J (nK hK u * x * (nK hK u)⁻¹) * nt hφ hK u := by
  rw [psi]
  split_ifs
  obtain ⟨c, hc, hγeq⟩ := (hΦ.exists_eq γ hγ).choose_spec.choose_spec
  exact rootMap_eq hφ hK hΦ π hπ hγ hc hγeq u hJ hsupp x.2

private theorem relationsHold_psi (π : G →* K) (hπ : ∀ J x, π (φ J x) = x)
    {S : Set (I → ℤ)} (hSΦ : S ⊆ Φ) (u : W) {J : Finset I} (hJ : J.card ≤ 2)
    (hsuppS : ∀ γ ∈ S, ∀ k ∉ J, ρ u γ k = 0) : RelationsHold X S (psi hφ hK hΦ) := by
  intro l hl hprod
  have key : ∀ p ∈ l, psi hφ hK hΦ p.1 p.2 =
      (nt hφ hK u)⁻¹ * fam φ J (nK hK u * (p.2 : K) * (nK hK u)⁻¹) * nt hφ hK u :=
    fun p hp => psi_eq hφ hK hΦ π hπ (hSΦ (hl p hp)) u hJ (hsuppS _ (hl p hp)) p.2
  have hmem : ∀ p ∈ l, nK hK u * (p.2 : K) * (nK hK u)⁻¹ ∈ levi X J := fun p hp =>
    X_le_levi hK hΦ (hΦ.smul_mem u _ (hSΦ (hl p hp))) (hsuppS _ (hl p hp))
      (conj_nK_mem hK hΦ u (hSΦ (hl p hp)) p.2.2)
  rw [List.map_congr_left key]
  have h1 : (l.map fun p => (nt hφ hK u)⁻¹ * fam φ J (nK hK u * (p.2 : K) * (nK hK u)⁻¹) *
      nt hφ hK u).prod =
      MulAut.conj (nt hφ hK u)⁻¹ (l.map fun p => fam φ J (nK hK u * (p.2 : K) *
        (nK hK u)⁻¹)).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp
  have h2 : (l.map fun p => fam φ J (nK hK u * (p.2 : K) * (nK hK u)⁻¹)) =
      (l.map fun p => nK hK u * (p.2 : K) * (nK hK u)⁻¹).map (fam φ J) := by
    rw [List.map_map]; rfl
  have h3 : (l.map fun p => nK hK u * (p.2 : K) * (nK hK u)⁻¹).prod =
      MulAut.conj (nK hK u) (l.map fun p => (p.2 : K)).prod := by
    rw [map_list_prod, List.map_map]
    rfl
  rw [h1, h2, ← fam_list_prod φ hJ _ (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hmem p hp), h3, hprod, map_one, fam_one φ hJ, map_one]

private theorem eq_fam_of_psi {Ψ : K →* G} (π : G →* K) (hπ : ∀ J x, π (φ J x) = x)
    (hΨ : ∀ γ ∈ Φ, ∀ x : X γ, Ψ x = psi hφ hK hΦ γ x) {J : Finset I} (hJ : J.card ≤ 2)
    {x : K} (hx : x ∈ levi X J) : Ψ x = fam φ J x := by
  let E : Subgroup K :=
    (MonoidHom.eqLocus (Ψ.comp (levi X J).subtype) (φ ⟨J, hJ⟩)).map (levi X J).subtype
  have hroot : ∀ j ∈ J, ∀ γ ∈ ({Pi.single j 1, -Pi.single j 1} : Set (I → ℤ)), X γ ≤ E := by
    intro j hj γ hγ y hy
    have hγΦ : γ ∈ Φ := by
      rcases hγ with rfl | rfl
      exacts [hΦ.single_mem j, neg_single_mem hΦ j]
    have hyr : y ∈ rankOne X j := by
      rcases hγ with rfl | rfl
      exacts [Subgroup.mem_sup_left hy, Subgroup.mem_sup_right hy]
    have hyJ : y ∈ levi X J := rankOne_le_levi X hj hyr
    refine ⟨⟨y, hyJ⟩, ?_, rfl⟩
    have hsupp : ∀ k ∉ ({j} : Finset I), ρ 1 γ k = 0 := by
      intro k hk
      rw [rho_one_apply]
      have hkj : k ≠ j := by simpa using hk
      rcases hγ with rfl | rfl <;> simp [Pi.single_eq_of_ne hkj]
    have h := psi_eq hφ hK hΦ π hπ hγΦ 1 (by simp) hsupp ⟨y, hy⟩
    simp only [nt_one, nK_one, inv_one, one_mul, mul_one] at h
    change Ψ y = φ ⟨J, hJ⟩ ⟨y, hyJ⟩
    rw [hΨ γ hγΦ ⟨y, hy⟩, h, fam_singleton_eq hφ hJ hj hyr, fam_of_mem φ hJ hyJ]
  have hle : levi X J ≤ E := iSup₂_le fun j hj =>
    sup_le (hroot j hj _ (by simp)) (hroot j hj _ (by simp))
  obtain ⟨x', hx', hxx'⟩ := hle hx
  have : x' = ⟨x, hx⟩ := Subtype.ext hxx'
  subst this
  rw [fam_of_mem φ hJ hx]
  exact hx'

end Family

section Main

variable [DecidableEq I] {M : CoxeterMatrix I} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {ρ : W →* Module.End ℤ (I → ℤ)} {Φ : Set (I → ℤ)} {K : Type u} [Group K]
  {X : (I → ℤ) → Subgroup K} {n : I → K} {H : I → Subgroup K}

theorem iSup_leviAmalgam_eq_top (hΦ : IsCTRootSystem cs ρ Φ)
    (hK : IsCTGroupDatum cs ρ Φ X n H) :
    ⨆ J : {J : Finset I // J.card ≤ 2}, leviAmalgam X J = ⊤ := by
  rw [eq_top_iff, ← hK.iSup_eq_top]
  refine iSup₂_le fun γ hγ x hx => ?_
  obtain ⟨w, i, c, hc, rfl⟩ := hΦ.exists_eq γ hγ
  set T := ⨆ J : {J : Finset I // J.card ≤ 2}, leviAmalgam X J
  have hlev : ∀ (J : Finset I) (hJ : J.card ≤ 2), levi X J ≤ T :=
    fun J hJ => le_iSup (leviAmalgam X) ⟨J, hJ⟩
  have hn : posLift cs n hK.braid w ∈ T :=
    posLift_mem cs n hK.braid T (fun l => hlev {l} (by simp) (mem_levi_singleton (hK.n_mem l))) w
  have hy := conj_nK_inv_mem hK hΦ w hγ hx
  have hwγ : ρ w⁻¹ (c • ρ w (Pi.single i 1)) = c • Pi.single i 1 := by
    rw [map_zsmul, ← rho_mul_apply, inv_mul_cancel, rho_one_apply]
  rw [hwγ] at hy
  have hci : c • Pi.single i 1 ∈ Φ := hwγ ▸ hΦ.smul_mem w⁻¹ _ hγ
  have hy' : (nK hK w)⁻¹ * x * nK hK w ∈ T := hlev {i} (by simp) (mem_levi_singleton
    (hK.le_rankOne i _ hci (fun k hk => by simp [Pi.single_eq_of_ne hk]) hy))
  have : x = nK hK w * ((nK hK w)⁻¹ * x * nK hK w) * (nK hK w)⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hn hy') (inv_mem hn)

theorem isUniversalCompletion_levi (hΦ : IsCTRootSystem cs ρ Φ)
    (hK : IsCTGroupDatum cs ρ Φ X n H) (rels : Set (Set (I → ℤ)))
    (hrels : ∀ S ∈ rels, S ⊆ Φ ∧
      ∃ (u : W) (J : Finset I), J.card ≤ 2 ∧ ∀ γ ∈ S, ∀ k ∉ J, ρ u γ k = 0)
    (hpres : IsPresentedBy.{u, max w u} Φ X rels) :
    IsUniversalCompletion.{u, _, w} (leviAmalgam X) := by
  intro G _ φ hφ
  let φ' : ∀ J : {J : Finset I // J.card ≤ 2}, levi X J.1 →* G × K :=
    fun J => (φ J).prod (levi X J.1).subtype
  have hφ' : IsCompatible (leviAmalgam X) φ' :=
    fun i j hij x y hxy => Prod.ext (hφ i j hij x y hxy) hxy
  have hπ' : ∀ J x, MonoidHom.snd G K (φ' J x) = x := fun _ _ => rfl
  obtain ⟨Ψ, hΨ⟩ := hpres (G × K) (psi hφ' hK hΦ) fun S hS => by
    obtain ⟨hSΦ, u, J, hJ, hsupp⟩ := hrels S hS
    exact relationsHold_psi hφ' hK hΦ _ hπ' hSΦ u hJ hsupp
  have hext : ∀ (J : {J : Finset I // J.card ≤ 2}) (x : levi X J.1), Ψ x = φ' J x := by
    intro J x
    rw [eq_fam_of_psi hφ' hK hΦ _ hπ' hΨ J.2 x.2, fam_of_mem φ' J.2 x.2]
  refine ⟨(MonoidHom.fst G K).comp Ψ, fun J x => ?_, fun ψ' hψ' => ?_⟩
  · simp [hext J x, φ']
  · refine hom_ext_of_iSup_eq_top (iSup_leviAmalgam_eq_top hΦ hK) fun J x => ?_
    rw [hψ' J x]
    simp [hext J x, φ']

end Main

end CFSG.LieType.CurtisTits
