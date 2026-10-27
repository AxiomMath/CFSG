module

public import Certificates.Data.Kernel.CosetLat.Defs
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.CosetLat

open CFSG.KC.Ord CFSG.KC.LQT.P
open CFSG.KC.Misc.Clos (ClosEnc clos_card treeAt sortAt closedAt letB_eq allN_iff andB_eq_true)

variable {Γ : Type*} [Group Γ] {enc : Γ → ℕ} {M : ℕ → ℕ → ℕ} {one : ℕ}

theorem notB_eq_true {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by simp [notB])

theorem getD_mem_closure (gens : List Γ) {j : ℕ} (hj : j < gens.length) :
    gens.getD j 1 ∈ Subgroup.closure {g | g ∈ gens} := by
  refine Subgroup.subset_closure ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

theorem wordG_mem (henc : ClosEnc enc M one) (gens : List Γ) {A : ℕ → ℕ}
    (hA : ∀ a < gens.length, A a = enc (gens.getD a 1)) {w : List ℕ}
    (hw : lettersG gens.length w = true) :
    ∃ g ∈ Subgroup.closure {g | g ∈ gens}, enc g = wordG M one A w := by
  induction w with
  | nil => exact ⟨1, Subgroup.one_mem _, henc.enc_one⟩
  | cons l w ih =>
    have hw' : andB (Nat.blt l gens.length) (lettersG gens.length w) = true := hw
    obtain ⟨hl, hw''⟩ := andB_eq_true hw'
    obtain ⟨g, hg, hge⟩ := ih hw''
    have hl' := Nat.blt_eq.mp hl
    refine ⟨gens.getD l 1 * g, Subgroup.mul_mem _ (getD_mem_closure gens hl') hg, ?_⟩
    change enc _ = M (A l) (wordG M one A w)
    rw [henc.enc_mul, hge, hA l hl']

theorem mem_of_wordAt (henc : ClosEnc enc M one) (gens : List Γ) {A : ℕ → ℕ}
    (hA : ∀ a < gens.length, A a = enc (gens.getD a 1)) {w : List ℕ} {x : Γ}
    (h : wordAt M one A gens.length w (enc x) = true) :
    x ∈ Subgroup.closure {g | g ∈ gens} := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  obtain ⟨g, hg, hge⟩ := wordG_mem henc gens hA h1
  rwa [henc.inj (hge.trans (Nat.eq_of_beq_eq_true h2))] at hg

theorem ctab_sound [Finite Γ] (henc : ClosEnc enc M one) (gens : List Γ) {G : ℕ → ℕ}
    (hG : ∀ j < gens.length, G j = enc (gens.getD j 1)) {T : Subgroup Γ} {nT nU : ℕ}
    {ET EU CR : ℕ → ℕ} (hT : ∀ k < nT, ∃ g ∈ T, enc g = ET k)
    (hU : ∀ i < nU, ∃ u : Γ, enc u = EU i) (h0 : 0 < nU) (h1 : Nat.beq (EU 0) one = true)
    (hc : ∀ i < nU, ctabAt M G gens.length ET nT EU nU CR i = true) :
    ∀ σ ∈ Subgroup.closure {g | g ∈ gens},
      ∃ t ∈ T, ∃ i < nU, ∃ u : Γ, enc u = EU i ∧ t * u = σ := by
  have key : ∀ σ ∈ Submonoid.closure {g | g ∈ gens},
      ∃ t ∈ T, ∃ i < nU, ∃ u : Γ, enc u = EU i ∧ t * u = σ := by
    intro σ hσ
    induction hσ using Submonoid.closure_induction_right with
    | one =>
      exact ⟨1, T.one_mem, 0, h0, 1, by rw [henc.enc_one, Nat.eq_of_beq_eq_true h1], by group⟩
    | mul_right x _ y hy ih =>
      obtain ⟨t, ht, i, hi, u, hu, rfl⟩ := ih
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
      have hci := hc i hi
      unfold ctabAt at hci
      have h := (allN_iff _ _).1 hci j hj
      rw [letB_eq, letB_eq, letB_eq] at h
      obtain ⟨hk, h⟩ := andB_eq_true h
      obtain ⟨hv, h⟩ := andB_eq_true h
      obtain ⟨t', ht', ht'e⟩ := hT _ (Nat.blt_eq.mp hk)
      obtain ⟨u', hu'⟩ := hU _ (Nat.blt_eq.mp hv)
      have hgj : G j = enc gens[j] := by
        rw [hG j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      have he : u' = t' * u * gens[j] := by
        apply henc.inj
        rw [hu', Nat.eq_of_beq_eq_true h, henc.enc_mul, henc.enc_mul, ht'e, hu, hgj]
      refine ⟨t * t'⁻¹, T.mul_mem ht (T.inv_mem ht'), _, Nat.blt_eq.mp hv, u', hu', ?_⟩
      rw [he]
      group
  intro σ hσ
  exact key σ (by rw [← Subgroup.closure_toSubmonoid_of_finite]; exact hσ)

theorem ctab_card [Finite Γ] (henc : ClosEnc enc M one) (gens : List Γ) {G : ℕ → ℕ}
    (hG : ∀ j < gens.length, G j = enc (gens.getD j 1)) {T : Subgroup Γ} {nT nU : ℕ}
    {ET EU CR : ℕ → ℕ} (hT : ∀ k < nT, ∃ g ∈ T, enc g = ET k)
    (hU : ∀ i < nU, ∃ u : Γ, enc u = EU i) (h0 : 0 < nU) (h1 : Nat.beq (EU 0) one = true)
    (hc : ∀ i < nU, ctabAt M G gens.length ET nT EU nU CR i = true) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) ≤ Nat.card T * nU := by
  classical
  have hs := ctab_sound henc gens hG hT hU h0 h1 hc
  choose! uf huf using hU
  let F : T × Fin nU → Γ := fun p => (p.1 : Γ) * uf p.2
  let f : {p : T × Fin nU // F p ∈ Subgroup.closure {g | g ∈ gens}} →
      Subgroup.closure {g | g ∈ gens} := fun p => ⟨F p.1, p.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    obtain ⟨t, ht, i, hi, u, hu, rfl⟩ := hs σ hσ
    have hu' : uf i = u := henc.inj ((huf i hi).trans hu.symm)
    have hF : F (⟨t, ht⟩, ⟨i, hi⟩) = t * u := by
      change t * uf i = t * u
      rw [hu']
    exact ⟨⟨(⟨t, ht⟩, ⟨i, hi⟩), hF ▸ hσ⟩, Subtype.ext hF⟩
  calc Nat.card (Subgroup.closure {g | g ∈ gens})
      ≤ Nat.card {p : T × Fin nU // F p ∈ Subgroup.closure {g | g ∈ gens}} :=
        Nat.card_le_card_of_surjective f hf
    _ ≤ Nat.card (T × Fin nU) := Finite.card_subtype_le _
    _ = Nat.card T * nU := by rw [Nat.card_prod, Nat.card_fin]

theorem trans_sound (henc : ClosEnc enc M one) {ρ : ℕ → Γ} {RC : ℕ → ℕ} {nR : ℕ}
    (hR : ∀ a < nR, enc (ρ a) = RC a) {T : Subgroup Γ} {nT nU : ℕ} {ET EU UR : ℕ → ℕ}
    (hT : ∀ k < nT, ∃ g ∈ T, enc g = ET k)
    (h : ∀ i < nU, transAt M RC nR ET nT EU UR i = true) :
    ∀ i < nU, ∃ a < nR, ∃ e ∈ T, enc (ρ a * e) = EU i := by
  intro i hi
  have h' := h i hi
  unfold transAt at h'
  rw [letB_eq, letB_eq, letB_eq] at h'
  obtain ⟨ha, h'⟩ := andB_eq_true h'
  obtain ⟨he, h'⟩ := andB_eq_true h'
  obtain ⟨e, heT, hee⟩ := hT _ (Nat.blt_eq.mp he)
  refine ⟨_, Nat.blt_eq.mp ha, e, heT, ?_⟩
  rw [henc.enc_mul, hR _ (Nat.blt_eq.mp ha), hee]
  exact (Nat.eq_of_beq_eq_true h').symm

theorem ctab_cover [Finite Γ] (henc : ClosEnc enc M one) (gens : List Γ) {G : ℕ → ℕ}
    (hG : ∀ j < gens.length, G j = enc (gens.getD j 1)) {T : Subgroup Γ} {nT nU nR : ℕ}
    {ρ : ℕ → Γ} {RC ET EU CR UR : ℕ → ℕ} (hR : ∀ a < nR, enc (ρ a) = RC a)
    (hT : ∀ k < nT, ∃ g ∈ T, enc g = ET k)
    (hu : ∀ i < nU, transAt M RC nR ET nT EU UR i = true) (h0 : 0 < nU)
    (h1 : Nat.beq (EU 0) one = true)
    (hc : ∀ i < nU, ctabAt M G gens.length ET nT EU nU CR i = true) :
    ∀ σ ∈ Subgroup.closure {g | g ∈ gens}, ∃ a < nR, ∃ π ∈ T, ∃ κ ∈ T, σ = π * ρ a * κ := by
  have ht := trans_sound henc hR hT hu
  have hU : ∀ i < nU, ∃ u : Γ, enc u = EU i := fun i hi => by
    obtain ⟨a, -, e, -, he⟩ := ht i hi
    exact ⟨_, he⟩
  intro σ hσ
  obtain ⟨t, htT, i, hi, u, hu', rfl⟩ := ctab_sound henc gens hG hT hU h0 h1 hc σ hσ
  obtain ⟨a, ha, e, heT, he⟩ := ht i hi
  refine ⟨a, ha, t, htT, e, heT, ?_⟩
  rw [henc.inj (hu'.trans he.symm), mul_assoc]

theorem notIn_sound (henc : ClosEnc enc M one) {T B : Subgroup Γ} {nT nU : ℕ}
    {ET EU : ℕ → ℕ} (hTx : ∀ g ∈ T, ∃ k < nT, enc g = ET k)
    (hBc : ∀ σ ∈ B, ∃ t ∈ T, ∃ i < nU, ∃ u : Γ, enc u = EU i ∧ t * u = σ) {x : Γ}
    (h : ∀ a < nU, notInAt M ET nT EU (enc x) a = true) : x ∉ B := by
  intro hx
  obtain ⟨t, ht, i, hi, u, hu, rfl⟩ := hBc x hx
  obtain ⟨k, hk, hke⟩ := hTx t ht
  have hk' := notB_eq_true ((allN_iff _ _).1 (h i hi) k hk)
  rw [← hke, ← hu, ← henc.enc_mul, Nat.beq_refl] at hk'
  exact absurd hk' (by simp)

theorem dvd_card_of_clos [Finite Γ] (henc : ClosEnc enc M one) {H : Subgroup Γ} {nK : ℕ}
    {K : ℕ → ℕ} (hK : ∀ j < nK, ∃ g ∈ H, enc g = K j) {N : ℕ} {E PA SG CT : ℕ → ℕ}
    (hN : 0 < N) (ht : ∀ k < N, treeAt M one K nK E PA k = true)
    (hs : ∀ i < N, sortAt N E SG i = true) (hcl : ∀ k < N, closedAt M K nK N E CT k = true) :
    N ∣ Nat.card H := by
  choose! g hgH hge using hK
  let gens : List Γ := (List.range nK).map g
  have hl : gens.length = nK := by simp [gens]
  have hG : ∀ j < gens.length, K j = enc (gens.getD j 1) := by
    intro j hj
    rw [hl] at hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact hj),
      Option.getD_some]
    simp only [gens, List.getElem_map, List.getElem_range]
    exact (hge j hj).symm
  obtain ⟨-, -, h3⟩ := clos_card henc gens hG hN (by rw [hl]; exact ht) hs
  obtain ⟨hcard, -⟩ := h3 (CT := CT) (by rw [hl]; exact hcl)
  have hle : Subgroup.closure {x | x ∈ gens} ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact hgH j (List.mem_range.1 hj)
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

theorem card_eq_of_dvd_of_le [Finite Γ] {H : Subgroup Γ} {N : ℕ} (hd : N ∣ Nat.card H)
    (hle : Nat.card H ≤ N) : Nat.card H = N :=
  le_antisymm hle (Nat.le_of_dvd Nat.card_pos hd)

theorem lat_overgroups_of [Finite Γ] {B Mt : Subgroup Γ} {Q : ℕ → Subgroup Γ} {nM nR i₀ : ℕ}
    {ρ : ℕ → Γ} (hi₀ : i₀ < nM) (hB : Q i₀ = B) (hBQ : ∀ i < nM, B ≤ Q i)
    (hcov : ∀ σ ∈ Mt, ∃ j < nR, ∃ π ∈ B, ∃ κ ∈ B, σ = π * ρ j * κ)
    (hrep : ∀ j < nR, ∃ t < nM, B ⊔ Subgroup.closure {ρ j} = Q t)
    (hjoin : ∀ a < nM, ∀ b < nM, ∃ c < nM, Q a ⊔ Q b = Q c) :
    ∀ Z : Subgroup Γ, B ≤ Z → Z ≤ Mt → ∃ i < nM, Q i = Z := by
  classical
  intro Z hBZ hZM
  let S := (Finset.range nM).filter fun i => Q i ≤ Z
  have hS : S.Nonempty := ⟨i₀, by simp [S, hi₀, hB, hBZ]⟩
  obtain ⟨i, hiS, hmax⟩ := S.exists_max_image (fun i => Nat.card (Q i)) hS
  simp only [S, Finset.mem_filter, Finset.mem_range] at hiS hmax
  refine ⟨i, hiS.1, le_antisymm hiS.2 fun σ hσ => ?_⟩
  by_contra hσQ
  obtain ⟨j, hj, π, hπ, κ, hκ, rfl⟩ := hcov _ (hZM hσ)
  obtain ⟨t, ht, hQt⟩ := hrep j hj
  obtain ⟨c, hc, hQc⟩ := hjoin i hiS.1 t ht
  have hρZ : ρ j ∈ Z := by
    have e : ρ j = π⁻¹ * (π * ρ j * κ) * κ⁻¹ := by group
    rw [e]
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem (hBZ hπ)) hσ) (Z.inv_mem (hBZ hκ))
  have hcZ : Q c ≤ Z := by
    rw [← hQc, ← hQt]
    refine sup_le hiS.2 (sup_le hBZ ?_)
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hρZ
  have hBc : B ≤ Q c := by
    rw [← hQc, ← hQt]
    exact le_sup_left.trans le_sup_right
  have hρc : ρ j ∈ Q c := by
    rw [← hQc, ← hQt]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.subset_closure rfl))
  have hσc : π * ρ j * κ ∈ Q c := (Q c).mul_mem ((Q c).mul_mem (hBc hπ) hρc) (hBc hκ)
  have hic : Q i ≤ Q c := by
    rw [← hQc]
    exact le_sup_left
  have hlt : Q i < Q c := lt_of_le_of_ne hic fun e => hσQ (e ▸ hσc)
  exact absurd (hmax c ⟨hc, hcZ⟩) (not_le.2 (Subgroup.card_lt_of_lt hlt))

end CFSG.KC.CosetLat

end
