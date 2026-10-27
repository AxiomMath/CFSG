module

public import CFSG.ClassicalInvolution.ModelFacts.CF3Sp
public import CFSG.ClassicalInvolution.Q3.Q3VFrameComm
public import CFSG.ClassicalInvolution.Q3.Q3VLocDef

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Frame

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {m : ℕ} {G : Type} [Group G]

section Model

variable {K : Type} [Field K] {n : ℕ}

theorem le_sup_stdPlane_of_orth {a b : Fin n} (hab : a ≠ b) {P : Submodule K (Fin n ⊕ Fin n → K)}
    (h : ∀ q, q ≠ a → q ≠ b → ∀ u ∈ P, ∀ v ∈ stdPlane K n q, form u v = 0) :
    P ≤ stdPlane K n a ⊔ stdPlane K n b := by
  intro v hv
  rw [mem_sup_stdPlane_iff hab]
  intro t ht
  obtain ⟨q, htq, hqa, hqb⟩ : ∃ q, t ∈ coords q ∧ q ≠ a ∧ q ≠ b := by
    rcases t with q | q
    · exact ⟨q, inl_mem_coords q, fun e => ht (Or.inl (e ▸ inl_mem_coords q)),
        fun e => ht (Or.inr (e ▸ inl_mem_coords q))⟩
    · exact ⟨q, inr_mem_coords q, fun e => ht (Or.inl (e ▸ inr_mem_coords q)),
        fun e => ht (Or.inr (e ▸ inr_mem_coords q))⟩
  have hs : (Pi.single (par t) 1 : Fin n ⊕ Fin n → K) ∈ stdPlane K n q := by
    rw [mem_stdPlane_iff]
    intro s hs
    have : s ≠ par t := fun e => hs (e ▸ parClosed_coords q t htq)
    simp [this]
  have h1 := h q hqa hqb v hv _ hs
  rw [form_single_right, par_par] at h1
  exact (mul_eq_zero.1 h1).resolve_right (sgn_ne_zero _)

theorem commute_of_le_sup_stdPlane {a b c : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {P : Submodule K (Fin n ⊕ Fin n → K)} (hP : P ≤ stdPlane K n a ⊔ stdPlane K n b)
    {x y : StatedSp n K} (hx : x ∈ planeGroup P) (hy : y ∈ planeGroup (stdPlane K n c)) :
    x * y = y * x := by
  have hx' : x ∈ suppGroup (coords a ∪ coords b) := planeGroup_le_suppGroup_pair hab hP hx
  rw [planeGroup_stdPlane, longRootSp2_eq_suppGroup] at hy
  have hsub : coords c ⊆ (coords a ∪ coords b)ᶜ := by
    intro t ht hmem
    rcases hmem with h | h
    · exact coords_subset_compl hca ht h
    · exact coords_subset_compl hcb ht h
  exact (commute_suppGroup_compl hx' (suppGroup_mono hsub hy)).eq

end Model

theorem exists_ne_eq_of_inj {l : Fin (m + 1)} {p : Fin (m + 1) → Fin m}
    (hpinj : ∀ c d, c ≠ l → d ≠ l → p c = p d → c = d) (q : Fin m) :
    ∃ c, c ≠ l ∧ p c = q := by
  have hinj : Function.Injective fun j : Fin m => p (l.succAbove j) := fun j j' e =>
    Fin.succAbove_right_injective
      (hpinj _ _ (Fin.succAbove_ne l j) (Fin.succAbove_ne l j') e)
  obtain ⟨j, hj⟩ := Finite.injective_iff_surjective.1 hinj q
  exact ⟨l.succAbove j, Fin.succAbove_ne l j, hj⟩

private theorem natCard_gf3 : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero]
  norm_num

theorem layerSub_eq (hm : 3 ≤ m) {Ω : Set (Subgroup G)} (hnonab : ∀ M ∈ Ω, ¬ Commutes M M)
    {K : Fin (m + 1) → Subgroup G} (_hK : IsMemberFrame Ω K) {l : Fin (m + 1)}
    {Θ : StatedSp m (GaloisField 3 1) →* G} (hΘ : IsLocLift m Ω (K l) Θ)
    (p : Fin (m + 1) → Fin m)
    (hp : ∀ c, c ≠ l → (planeGroup (stdPlane (GaloisField 3 1) m (p c))).map Θ = K c)
    (hpinj : ∀ c d, c ≠ l → d ≠ l → p c = p d → c = d)
    {a b : Fin (m + 1)} (ha : a ≠ l) (hb : b ≠ l) (_hab : a ≠ b) (hpab : p a ≠ p b) :
    layerSub Ω K a b = (pairEmbed (GaloisField 3 1) hpab).range.map Θ := by
  have hrange : (pairEmbed (GaloisField 3 1) hpab).range =
      pairPlaneSubgroup (GaloisField 3 1) m (p a) (p b) := by
    rw [range_pairEmbed, pairPlaneSubgroup_eq3 natCard_gf3 hpab]
  rw [hrange, pairPlaneSubgroup, Subgroup.map_iSup]
  apply le_antisymm
  · unfold layerSub
    refine iSup₂_le fun M hM => ?_
    obtain ⟨hMΩ, hMc⟩ := hM
    have hMl : Commutes M (K l) := hMc l (Ne.symm ha) (Ne.symm hb)
    have hMne : M ≠ K l := by
      intro e
      rw [e] at hMl
      exact hnonab (K l) (e ▸ hMΩ) hMl
    obtain ⟨P, hP, hMP⟩ := hΘ.members M hMΩ hMne hMl
    have hle : P ≤ stdPlane (GaloisField 3 1) m (p a) ⊔ stdPlane (GaloisField 3 1) m (p b) := by
      refine le_sup_stdPlane_of_orth hpab fun q hqa hqb u hu v hv => ?_
      obtain ⟨c, hcl, hcq⟩ := exists_ne_eq_of_inj hpinj q
      have hca : c ≠ a := fun e => hqa (by rw [← hcq, e])
      have hcb : c ≠ b := fun e => hqb (by rw [← hcq, e])
      have hcomm := hMc c hca hcb
      rw [hMP, ← hp c hcl, hcq] at hcomm
      exact (commutes_map_planeGroup_iff hm hΘ.ker_le hP
        (isHyperbolicPlane_stdPlane q)).1 hcomm u hu v hv
    rw [hMP]
    exact le_iSup (fun Q : pairPlanes (GaloisField 3 1) m (p a) (p b) =>
      (planeGroup (Q : Submodule (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1))).map Θ)
      ⟨P, hP, hle⟩
  · unfold layerSub
    refine iSup_le fun P => ?_
    obtain ⟨hPh, hPle⟩ := P.2
    refine le_iSup₂_of_le ((planeGroup (P : Submodule (GaloisField 3 1)
      (Fin m ⊕ Fin m → GaloisField 3 1))).map Θ) ⟨hΘ.plane_mem _ hPh, fun c hca hcb => ?_⟩ le_rfl
    by_cases hcl : c = l
    · rw [hcl]
      exact fun x hx y hy => hΘ.comm x (Subgroup.map_le_range _ _ hx) y hy
    · rw [← hp c hcl]
      have hpa : p c ≠ p a := fun e => hca (hpinj c a hcl ha e)
      have hpb : p c ≠ p b := fun e => hcb (hpinj c b hcl hb e)
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, commute_of_le_sup_stdPlane hpab hpa hpb hPle hx hy]

theorem IsLabLift.layerSub_eq (hm : 3 ≤ m) {Ω : Set (Subgroup G)}
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {K : Fin (m + 1) → Subgroup G} (hK : IsMemberFrame Ω K)
    {l : Fin (m + 1)} {Θ : StatedSp m (GaloisField 3 1) →* G} (hΘ : IsLabLift m Ω K l Θ)
    {i j : Fin m} (hij : i ≠ j) {a b : Fin (m + 1)} (ha : l.succAbove i = a)
    (hb : l.succAbove j = b) :
    layerSub Ω K a b = (pairEmbed (GaloisField 3 1) hij).range.map Θ := by
  subst ha hb
  have : Nonempty (Fin m) := ⟨i⟩
  have hpl : ∀ j, Function.invFun l.succAbove (l.succAbove j) = j :=
    Function.leftInverse_invFun Fin.succAbove_right_injective
  have hp : ∀ c, c ≠ l →
      (planeGroup (stdPlane (GaloisField 3 1) m (Function.invFun l.succAbove c))).map Θ = K c := by
    intro c hc
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hc
    rw [hpl]
    exact hΘ.lab j'
  have hpinj : ∀ c d, c ≠ l → d ≠ l →
      Function.invFun l.succAbove c = Function.invFun l.succAbove d → c = d := by
    intro c d hc hd e
    obtain ⟨c', rfl⟩ := Fin.exists_succAbove_eq hc
    obtain ⟨d', rfl⟩ := Fin.exists_succAbove_eq hd
    rw [hpl, hpl] at e
    rw [e]
  have hpab : Function.invFun l.succAbove (l.succAbove i) ≠
      Function.invFun l.succAbove (l.succAbove j) := by
    rw [hpl, hpl]
    exact hij
  have h := Frame.layerSub_eq hm hnonab hK hΘ.loc (Function.invFun l.succAbove) hp hpinj
    (Fin.succAbove_ne l i) (Fin.succAbove_ne l j)
    (fun e => hij (Fin.succAbove_right_injective e)) hpab
  have key : ∀ (x y : Fin m) (hxy : x ≠ y), x = i → y = j →
      (pairEmbed (GaloisField 3 1) hxy).range.map Θ =
        (pairEmbed (GaloisField 3 1) hij).range.map Θ := by
    rintro x y hxy rfl rfl
    rfl
  rw [h]
  exact key _ _ _ (hpl i) (hpl j)

theorem layerSub_le_centralizer {Ω : Set (Subgroup G)} {K : Fin (m + 1) → Subgroup G}
    {a b c : Fin (m + 1)} (hca : c ≠ a) (hcb : c ≠ b) :
    ∀ x ∈ layerSub Ω K a b, ∀ y ∈ K c, x * y = y * x := by
  have h : layerSub Ω K a b ≤ Subgroup.centralizer (K c : Set G) := by
    unfold layerSub
    refine iSup₂_le fun M hM x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hM.2 c hca hcb x hx y hy).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h hx) y hy).symm

end CFSG.ClassicalInvolution.Q3.Q3V.Frame
