module

public import CFSG.ClassicalInvolution.Q3.TL3T35
public import CFSG.ClassicalInvolution.Q3.TL3T34

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4

section Model

variable {n : ℕ}

theorem modPi_zero_of_alt (hn : 5 ≤ n) {u : Fin n → ZMod 2}
    (h : ∀ σ ∈ alternatingGroup (Fin n), ModPi (actV σ u) u) : ModPi u 0 := by
  classical
  have hconst : ∀ i j : Fin n, u i = u j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, hki, hkj, -, -⟩ := exists_ne_four hn i j i j
    obtain ⟨p, hpi, hpj, hpk, -⟩ := exists_ne_four hn i j k k
    set σ : Equiv.Perm (Fin n) := Equiv.swap i k * Equiv.swap i j with hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, hσ, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap (Ne.symm hki), Equiv.Perm.sign_swap hij]
      decide
    have hσp : σ p = p := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpi hpj,
        Equiv.swap_apply_of_ne_of_ne hpi hpk]
    have hσi : σ i = j := by
      rw [hσ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) (fun e => hkj e.symm)
    have hσi' : σ.symm j = i := by rw [← hσi, Equiv.symm_apply_apply]
    have hσp' : σ.symm p = p := by rw [Equiv.symm_apply_eq, hσp]
    rcases h σ hσA with e | e
    · have := congrFun e j
      simp only [actV] at this
      rw [hσi'] at this
      exact this
    · exfalso
      have := congrFun e p
      simp only [actV, Pi.add_apply, Pi.one_apply] at this
      rw [hσp'] at this
      revert this
      generalize u p = c
      revert c
      decide
  have hn0 : 0 < n := by omega
  set o : Fin n := ⟨0, hn0⟩
  have hu : u = fun _ => u o := funext fun i => hconst i o
  have : u o = 0 ∨ u o = 1 := by
    generalize u o = c
    revert c
    decide
  rcases this with h0 | h1
  · left
    rw [hu, h0]
    rfl
  · right
    rw [hu, h1, zero_add]
    rfl

theorem aeModel_center (hn : 5 ≤ n) : ModelCenter (TL4.aeModel n) := by
  rw [TL4.aeModel_eq]
  intro m _ hc
  obtain ⟨a, rfl⟩ : ∃ a, mkQ n a = m := QuotientGroup.mk_surjective m
  have hσ : a.perm = 1 := by
    refine perm_eq_one_of_modPi hn fun p q _ => ?_
    have hv : vbar n (pairVec p q) ∈ aeBarOver (alternatingGroup (Fin n)) :=
      vbar_mem_aeBarOver (sum_pairVec p q)
    have h1 : mkQ n a * vbar n (pairVec p q) * (mkQ n a)⁻¹ = vbar n (pairVec p q) := by
      rw [hc _ hv, mul_inv_cancel_right]
    rw [conj_vbar (permBar_mkQ a)] at h1
    exact vbar_eq_iff.mp h1
  obtain ⟨u, hu⟩ := exists_vbar_of_permBar_eq_one
    (show permBar n (mkQ n a) = 1 by rw [permBar_mkQ, hσ])
  rw [hu] at hc ⊢
  have hfix : ∀ σ ∈ alternatingGroup (Fin n), ModPi (actV σ u) u := fun σ hσ' => by
    have hσM := mkQ_ofPerm_mem_aeBarOver hσ' hσ'
    have h1 : mkQ n (ofPerm σ) * vbar n u * (mkQ n (ofPerm σ))⁻¹ = vbar n u := by
      rw [← hc _ hσM, mul_inv_cancel_right]
    rw [conj_vbar (permBar_mkQ (ofPerm σ))] at h1
    exact vbar_eq_iff.mp h1
  rw [← vbar_zero]
  exact vbar_eq_iff.mpr (modPi_zero_of_alt hn hfix)

@[expose] def indv (α : Finset (Fin n)) : Fin n → ZMod 2 := fun x => if x ∈ α then 1 else 0

theorem zBar_eq_vbar_indv (α : Finset (Fin n)) (h : α.card = 4) : zBar α h = vbar n (indv α) := by
  rw [zBar, vbar]
  congr 1
  refine Wr.ext (funext fun x => ?_) (zOf_perm _)
  have hr : x ∈ Set.range (emb α h) ↔ x ∈ α := by rw [range_emb]; rfl
  rw [zOf_vec_apply]
  show _ = if x ∈ α then 1 else 0
  by_cases hx : x ∈ α
  · have : x ∈ Set.range (emb α h) := hr.mpr hx
    simp [this, hx]
  · have : x ∉ Set.range (emb α h) := fun h' => hx (hr.mp h')
    simp [this, hx]

theorem actV_indv (σ : Equiv.Perm (Fin n)) (α : Finset (Fin n)) :
    actV σ (indv α) = indv (α.map σ.toEmbedding) := by
  funext x
  simp only [actV, indv, Finset.mem_map_equiv]

theorem conj_zBar_ofPerm (σ : Equiv.Perm (Fin n)) (α : Finset (Fin n)) (h : α.card = 4)
    (h' : (α.map σ.toEmbedding).card = 4) :
    mkQ n (ofPerm σ) * zBar α h * (mkQ n (ofPerm σ))⁻¹ = zBar (α.map σ.toEmbedding) h' := by
  rw [zBar_eq_vbar_indv, zBar_eq_vbar_indv, conj_vbar (permBar_mkQ (ofPerm σ))]
  exact congrArg (vbar n) (actV_indv σ α)

theorem exists_alt_map_eq {α β : Finset (Fin n)} (hα : α.card = 4)
    (hβ : β.card = 4) : ∃ σ ∈ alternatingGroup (Fin n), α.map σ.toEmbedding = β := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq α β (by rw [hα, hβ])
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr h1, hσ⟩
  ·
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ β, ∃ b ∈ β, a ≠ b := by
      have : 1 < β.card := by rw [hβ]; norm_num
      exact Finset.one_lt_card.mp this
    refine ⟨Equiv.swap a b * σ, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, h1]
      decide
    · have e : α.map (Equiv.swap a b * σ).toEmbedding =
          (α.map σ.toEmbedding).map (Equiv.swap a b).toEmbedding := by
        rw [Finset.map_map]
        rfl
      rw [e, hσ]
      ext x
      rw [Finset.mem_map_equiv, Equiv.symm_swap]
      by_cases hxa : x = a
      · subst hxa
        rw [Equiv.swap_apply_left]
        exact ⟨fun _ => ha, fun _ => hb⟩
      · by_cases hxb : x = b
        · subst hxb
          rw [Equiv.swap_apply_right]
          exact ⟨fun _ => hb, fun _ => ha⟩
        · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem permBar_eq_permQ (x : AEQ n) : permBar n x = permQ n x := by
  obtain ⟨a, rfl⟩ : ∃ a, mkQ n a = x := QuotientGroup.mk_surjective x
  rw [permBar_mkQ, permQ_mkQ]

theorem comm_of_mem_ker_permQ {x y : AEQ n} (hx : permQ n x = 1) (hy : permQ n y = 1) :
    x * y = y * x := by
  obtain ⟨u, rfl⟩ := exists_vbar_of_permBar_eq_one (n := n) (g := x) (by rw [permBar_eq_permQ, hx])
  obtain ⟨w, rfl⟩ := exists_vbar_of_permBar_eq_one (n := n) (g := y) (by rw [permBar_eq_permQ, hy])
  rw [← vbar_add, ← vbar_add, add_comm]

theorem mem_aeModel_ofPerm {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    mkQ n (ofPerm σ) ∈ TL4.aeModel n := by
  rw [TL4.aeModel_eq]
  exact mkQ_ofPerm_mem_aeBarOver hσ hσ

theorem zBar_mem_aeModel (α : Finset (Fin n)) (h : α.card = 4) : zBar α h ∈ TL4.aeModel n := by
  classical
  rw [zBar_eq_vbar_indv, TL4.aeModel_eq]
  refine vbar_mem_aeBarOver ?_
  simp only [indv, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, h]
  decide

theorem mem_of_zBar_mem (hn : 5 ≤ n) {H : Subgroup (AEQ n)}
    (hH : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4), zBar δ hδ ∈ H) {u : Fin n → ZMod 2}
    (hu : ∑ i, u i = 0) : mkQ n (ofVec u) ∈ H := by
  classical
  refine mem_of_pairVec (fun j k hjk => ?_) hu
  obtain ⟨a, haj, hak, -, -⟩ := exists_ne_four hn j k j k
  obtain ⟨b, hbj, hbk, hba, -⟩ := exists_ne_four hn j k a a
  obtain ⟨c, hcj, hck, hca, hcb⟩ := exists_ne_four hn j k a b
  have h1 : ({j, a, b, c} : Finset (Fin n)).card = 4 :=
    card_four (Ne.symm haj) (Ne.symm hbj) (Ne.symm hcj) (Ne.symm hba) (Ne.symm hca) (Ne.symm hcb)
  have h2 : ({k, a, b, c} : Finset (Fin n)).card = 4 :=
    card_four (Ne.symm hak) (Ne.symm hbk) (Ne.symm hck) (Ne.symm hba) (Ne.symm hca) (Ne.symm hcb)
  have hv : pairVec j k = indv {j, a, b, c} + indv {k, a, b, c} := by
    funext x
    simp only [pairVec, indv, Pi.add_apply, Pi.single_apply, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hxj : x = j
    · subst hxj
      simp [hjk, haj.symm, hbj.symm, hcj.symm]
    by_cases hxk : x = k
    · subst hxk
      simp [hxj, hak.symm, hbk.symm, hck.symm]
    by_cases hxa : x = a
    · subst hxa
      simp [hxj, hxk]
      decide
    by_cases hxb : x = b
    · subst hxb
      simp [hxj, hxk, hxa]
      decide
    by_cases hxc : x = c
    · subst hxc
      simp [hxj, hxk, hxa, hxb]
      decide
    simp [hxj, hxk, hxa, hxb, hxc]
  have := H.mul_mem (hH _ h1) (hH _ h2)
  rw [zBar_eq_vbar_indv, zBar_eq_vbar_indv, ← vbar_add, ← hv] at this
  exact this

theorem aut_eq_one_of_fix (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) (hθ : ∃ k : ℕ, θ ^ 3 ^ k = 1)
    (hperm : ∀ x : ↥(TL4.aeModel n), permQ n (θ x) = permQ n x) {γ : Finset (Fin n)}
    (hγ : γ.card = 4)
    (hz : θ ⟨zBar γ hγ, zBar_mem_aeModel γ hγ⟩ = ⟨zBar γ hγ, zBar_mem_aeModel γ hγ⟩) :
    θ = 1 := by
  classical
  have hconj : ∀ x v : ↥(TL4.aeModel n), permQ n v = 1 → θ (x * v * x⁻¹) = x * θ v * x⁻¹ := by
    intro x v hv
    have he : permQ n ((x⁻¹ * θ x : ↥(TL4.aeModel n)) : AEQ n) = 1 := by
      push_cast
      rw [map_mul, map_inv, hperm, inv_mul_cancel]
    have hθv : permQ n (θ v : AEQ n) = 1 := by rw [hperm]; exact hv
    have hc := comm_of_mem_ker_permQ he hθv
    rw [map_mul, map_mul, map_inv]
    have e1 : θ x = x * (x⁻¹ * θ x) := by group
    rw [e1]
    apply Subtype.ext
    push_cast
    have hc' : ((x : AEQ n)⁻¹ * (θ x : AEQ n)) * (θ v : AEQ n) =
        (θ v : AEQ n) * ((x : AEQ n)⁻¹ * (θ x : AEQ n)) := by
      have := hc
      push_cast at this
      exact this
    calc (x : AEQ n) * ((x : AEQ n)⁻¹ * (θ x : AEQ n)) * (θ v : AEQ n) *
          ((x : AEQ n) * ((x : AEQ n)⁻¹ * (θ x : AEQ n)))⁻¹ =
        (x : AEQ n) * (((x : AEQ n)⁻¹ * (θ x : AEQ n)) * (θ v : AEQ n)) *
          ((x : AEQ n)⁻¹ * (θ x : AEQ n))⁻¹ * (x : AEQ n)⁻¹ := by group
      _ = (x : AEQ n) * ((θ v : AEQ n) * ((x : AEQ n)⁻¹ * (θ x : AEQ n))) *
          ((x : AEQ n)⁻¹ * (θ x : AEQ n))⁻¹ * (x : AEQ n)⁻¹ := by rw [hc']
      _ = (x : AEQ n) * (θ v : AEQ n) * (x : AEQ n)⁻¹ := by group
  have hpz : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4), permQ n (zBar δ hδ) = 1 := fun δ hδ => by
    rw [zBar, permQ_mkQ, zOf_perm]
  have hzδ : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4),
      θ ⟨zBar δ hδ, zBar_mem_aeModel δ hδ⟩ = ⟨zBar δ hδ, zBar_mem_aeModel δ hδ⟩ := by
    intro δ hδ
    obtain ⟨σ, hσ, hσδ⟩ := exists_alt_map_eq hγ hδ
    subst hσδ
    set x : ↥(TL4.aeModel n) := ⟨mkQ n (ofPerm σ), mem_aeModel_ofPerm hσ⟩ with hx
    have hz' : (⟨zBar (γ.map σ.toEmbedding) hδ, zBar_mem_aeModel _ hδ⟩ : ↥(TL4.aeModel n)) =
        x * ⟨zBar γ hγ, zBar_mem_aeModel γ hγ⟩ * x⁻¹ := by
      apply Subtype.ext
      push_cast
      exact (conj_zBar_ofPerm σ γ hγ hδ).symm
    rw [hz', hconj x _ (hpz γ hγ), hz]
  set F : Subgroup (AEQ n) :=
    (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _)).map (TL4.aeModel n).subtype with hF
  have hmem : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4), zBar δ hδ ∈ F := fun δ hδ =>
    ⟨⟨zBar δ hδ, zBar_mem_aeModel δ hδ⟩, hzδ δ hδ, rfl⟩
  have hvec : ∀ v : ↥(TL4.aeModel n), permQ n v = 1 → θ v = v := by
    intro v hv
    obtain ⟨a, ha, hav⟩ := v.2
    have hap : a.perm = 1 := by rw [← permQ_mkQ, hav]; exact hv
    have ha' : a = ofVec a.vec := Wr.ext rfl hap
    have hsum : ∑ i, a.vec i = 0 := ha.1
    have := mem_of_zBar_mem hn hmem hsum
    rw [← ha', hav] at this
    obtain ⟨w, hw, hwv⟩ := this
    have hw' : w = v := Subtype.ext hwv
    rw [← hw']
    exact hw
  have hsq : θ ^ 2 = 1 := by
    ext x
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    set e : ↥(TL4.aeModel n) := x⁻¹ * θ x with he
    have hep : permQ n e = 1 := by
      rw [he]
      push_cast
      rw [map_mul, map_inv, hperm, inv_mul_cancel]
    have hθe := hvec e hep
    have hee : e * e = 1 := Subtype.ext (mul_self_of_mem_ker_permQ hep)
    have e1 : θ x = x * e := by rw [he]; group
    rw [e1, map_mul, hθe, e1, mul_assoc, hee, mul_one]
  obtain ⟨k, hk⟩ := hθ
  have h1 : orderOf θ = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num))
    (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hk)
  exact orderOf_eq_one_iff.mp h1

theorem sq_eq_one_of_comm_d : ∀ c : Equiv.Perm (Fin 4), c * d₁ = d₁ * c → c * d₂ = d₂ * c →
    c * d₃ = d₃ * c → c * c = 1 := by
  decide

theorem fix_of_comm_embedPerm (ι : Fin 4 ↪ Fin n) {σ : Equiv.Perm (Fin n)}
    (hσ3 : ∃ k : ℕ, σ ^ 3 ^ k = 1) (h1 : σ * embedPerm ι d₁ = embedPerm ι d₁ * σ)
    (h2 : σ * embedPerm ι d₂ = embedPerm ι d₂ * σ)
    (h3 : σ * embedPerm ι d₃ = embedPerm ι d₃ * σ) : ∀ i, σ (ι i) = ι i := by
  classical
  have hsupp : ∀ x, x ∈ Set.range ι ↔ embedPerm ι d₁ x ≠ x := by
    intro x
    constructor
    · rintro ⟨i, rfl⟩
      rw [embedPerm_apply]
      intro h
      exact (by decide : ∀ i : Fin 4, d₁ i ≠ i) i (ι.injective h)
    · intro h
      by_contra hx
      exact h (embedPerm_of_not_mem ι _ hx)
  have hmap : ∀ i, σ (ι i) ∈ Set.range ι := by
    intro i
    rw [hsupp]
    intro h
    have e := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) h1
    simp only [Equiv.Perm.mul_apply] at e
    rw [← e] at h
    have := σ.injective h
    exact ((hsupp (ι i)).mp ⟨i, rfl⟩) this
  set c := localPerm ι σ hmap with hc
  have hcσ : ∀ i, σ (ι i) = ι (c i) := localPerm_spec ι σ hmap
  have hcomm : ∀ d : Equiv.Perm (Fin 4), σ * embedPerm ι d = embedPerm ι d * σ →
      c * d = d * c := by
    intro d hd
    refine Equiv.ext fun i => ι.injective ?_
    have e := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) hd
    simp only [Equiv.Perm.mul_apply] at e
    rw [embedPerm_apply, hcσ, hcσ, embedPerm_apply] at e
    simp only [Equiv.Perm.mul_apply]
    exact e
  have hcc := sq_eq_one_of_comm_d c (hcomm _ h1) (hcomm _ h2) (hcomm _ h3)
  obtain ⟨k, hk⟩ := hσ3
  have hpow : ∀ m : ℕ, ∀ i, (σ ^ m) (ι i) = ι ((c ^ m) i) := by
    intro m
    induction m with
    | zero => intro i; rfl
    | succ m ih =>
      intro i
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hcσ, pow_succ', Equiv.Perm.mul_apply]
  have hck : c ^ 3 ^ k = 1 := by
    refine Equiv.ext fun i => ι.injective ?_
    rw [← hpow, hk]
    rfl
  have hc1 : c = 1 := by
    have h2' : c ^ 2 = 1 := by rw [pow_two]; exact hcc
    have := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one h2') (orderOf_dvd_of_pow_eq_one hck)
    exact orderOf_eq_one_iff.mp this
  intro i
  rw [hcσ, hc1]
  rfl

theorem perm_eq_one_of_fix (hn : 5 ≤ n) (hn7 : n ≠ 7) {σ : Equiv.Perm (Fin n)}
    (hσk : ∃ k : ℕ, σ ^ 3 ^ k = 1) {γ : Finset (Fin n)} (hγ : γ.card = 4)
    (hσγ : ∀ x ∈ γ, σ x = x)
    (hσβ : ∀ β : Finset (Fin n), β.card = 4 → Disjoint β γ → ∀ x ∈ β, σ x = x) : σ = 1 := by
  classical
  have hσc : ∀ x, x ∉ γ → σ x ∉ γ := fun x hx h => hx (σ.injective (hσγ _ h) ▸ h)
  have hcard : γᶜ.card = n - 4 := by rw [Finset.card_compl, hγ, Fintype.card_fin]
  rcases eq_or_ne n 6 with rfl | hn6
  ·
    have hsq : σ ^ 2 = 1 := by
      refine Equiv.ext fun x => ?_
      rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      by_cases hx : x ∈ γ
      · rw [hσγ x hx, hσγ x hx]
      obtain ⟨a, b, -, hγc⟩ := Finset.card_eq_two.mp (by rw [hcard] : γᶜ.card = 2)
      have hmem : ∀ y, y ∉ γ → y = a ∨ y = b := fun y hy => by
        have : y ∈ γᶜ := Finset.mem_compl.mpr hy
        rw [hγc] at this
        simpa using this
      by_cases hfx : σ x = x
      · rw [hfx, hfx]
      have hne : σ (σ x) ≠ σ x := fun h => hfx (σ.injective h)
      rcases hmem x hx with h1 | h1 <;> rcases hmem _ (hσc x hx) with h2 | h2 <;>
        rcases hmem _ (hσc _ (hσc x hx)) with h3 | h3 <;>
        first
        | exact h3.trans h1.symm
        | exact absurd (h2.trans h1.symm) hfx
        | exact absurd (h3.trans h2.symm) hne
    obtain ⟨k, hk⟩ := hσk
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one hsq)
      (orderOf_dvd_of_pow_eq_one hk))
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.one_apply]
  by_cases hx : x ∈ γ
  · exact hσγ x hx
  rcases (show n = 5 ∨ 8 ≤ n by omega) with rfl | h8
  ·
    have hxc : x ∈ γᶜ := Finset.mem_compl.mpr hx
    have hσxc : σ x ∈ γᶜ := Finset.mem_compl.mpr (hσc x hx)
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (by rw [hcard] : γᶜ.card = 1)
    rw [hy, Finset.mem_singleton] at hxc hσxc
    rw [hσxc, hxc]
  ·
    have hxc : x ∈ γᶜ := Finset.mem_compl.mpr hx
    have h3 : 3 ≤ (γᶜ.erase x).card := by
      rw [Finset.card_erase_of_mem hxc, hcard]
      omega
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h3
    have hxt : x ∉ t := fun h => by simpa using ht h
    refine hσβ (insert x t) (by rw [Finset.card_insert_of_notMem hxt, htc]) ?_ x
      (Finset.mem_insert_self x t)
    rw [Finset.disjoint_left]
    intro y hy hyγ
    rcases Finset.mem_insert.mp hy with rfl | hyt
    · exact hx hyγ
    · have := ht hyt
      rw [Finset.mem_erase, Finset.mem_compl] at this
      exact this.2 hyγ

theorem memBar_le_aeModel (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    memBar α h b ≤ TL4.aeModel n := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨k, ?_, rfl⟩
  cases b
  · obtain ⟨a, ha, rfl⟩ := hk
    exact embed_mem_aeSub _ (kStarList_even a ha)
  · obtain ⟨a, ha, rfl⟩ := hk
    exact embed_mem_aeSub _ (kList_even a ha)

theorem permQ_mem_alt {x : AEQ n} (hx : x ∈ TL4.aeModel n) :
    permQ n x ∈ alternatingGroup (Fin n) := by
  rw [TL4.aeModel_eq] at hx
  exact permQ_mem_of_mem_aeBarOver hx

theorem permQ_aut_eq_one (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) {v : ↥(TL4.aeModel n)}
    (hv : permQ n v = 1) : permQ n (θ v) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' : Subgroup ↥(TL4.aeModel n) := ((permQ n).comp (TL4.aeModel n).subtype).ker with hE'
  set T : Subgroup (AEQ n) := (E'.map θ.toMonoidHom).map (TL4.aeModel n).subtype with hT
  have hTM : T ≤ aeBarOver (alternatingGroup (Fin n)) := by
    rw [← TL4.aeModel_eq]
    exact Subgroup.map_subtype_le _
  have hTn : ∀ x ∈ aeBarOver (alternatingGroup (Fin n)), ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
    rintro x hx _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    rw [← TL4.aeModel_eq] at hx
    refine ⟨θ (θ.symm ⟨x, hx⟩ * e * (θ.symm ⟨x, hx⟩)⁻¹), ⟨_, ?_, rfl⟩, ?_⟩
    · show permQ n ((θ.symm ⟨x, hx⟩ * e * (θ.symm ⟨x, hx⟩)⁻¹ : ↥(TL4.aeModel n)) : AEQ n) = 1
      push_cast
      have he' : permQ n (e : AEQ n) = 1 := he
      rw [map_mul, map_mul, map_inv, he', mul_one, mul_inv_cancel]
    · show ((θ (θ.symm ⟨x, hx⟩ * e * (θ.symm ⟨x, hx⟩)⁻¹) : ↥(TL4.aeModel n)) : AEQ n) =
        x * (θ e : AEQ n) * x⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
  have hE2 : IsPGroup 2 ↥E' := fun e => ⟨1, by
    rw [pow_one, pow_two]
    have he : permQ n ((e : ↥(TL4.aeModel n)) : AEQ n) = 1 := e.2
    exact Subtype.ext (Subtype.ext (mul_self_of_mem_ker_permQ he))⟩
  have hT2 : IsPGroup 2 ↥T := (hE2.map _).map _
  have hle := le_ker_permQ_of_normal (A := alternatingGroup (Fin n)) le_rfl
    (fun N hNA hNn hN2 => eq_bot_of_normal_two_alternating hn hNA hNn hN2) hTM hTn hT2
  exact hle ⟨θ v, ⟨v, hv, rfl⟩, rfl⟩

@[expose] noncomputable def autAltHom (θ : MulAut ↥(TL4.aeModel n)) :
    alternatingGroup (Fin n) →* alternatingGroup (Fin n) where
  toFun τ := ⟨permQ n (θ ⟨mkQ n (ofPerm τ), mem_aeModel_ofPerm τ.2⟩), permQ_mem_alt (θ _).2⟩
  map_one' := by
    apply Subtype.ext
    have e : (⟨mkQ n (ofPerm ((1 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))),
        mem_aeModel_ofPerm (1 : alternatingGroup (Fin n)).2⟩ : ↥(TL4.aeModel n)) = 1 :=
      Subtype.ext (by
        show mkQ n (ofPerm 1) = 1
        rw [show ofPerm (1 : Equiv.Perm (Fin n)) = 1 from rfl, map_one])
    simp only [e, map_one]
    rfl
  map_mul' τ τ' := by
    apply Subtype.ext
    have e : (⟨mkQ n (ofPerm ((τ * τ' : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))),
        mem_aeModel_ofPerm (τ * τ').2⟩ : ↥(TL4.aeModel n)) =
        ⟨mkQ n (ofPerm τ), mem_aeModel_ofPerm τ.2⟩ * ⟨mkQ n (ofPerm τ'), mem_aeModel_ofPerm τ'.2⟩ :=
      Subtype.ext (by
        show mkQ n (ofPerm ((τ : Equiv.Perm (Fin n)) * τ')) = mkQ n (ofPerm τ) * mkQ n (ofPerm τ')
        rw [← ofPerm_mul, map_mul])
    show permQ n (θ _ : AEQ n) = permQ n (θ _ : AEQ n) * permQ n (θ _ : AEQ n)
    rw [e, map_mul, Subgroup.coe_mul, map_mul]

theorem permQ_aut_apply (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) (x : ↥(TL4.aeModel n)) :
    permQ n (θ x) = (autAltHom θ ⟨permQ n x, permQ_mem_alt x.2⟩ : Equiv.Perm (Fin n)) := by
  set xτ : ↥(TL4.aeModel n) := ⟨mkQ n (ofPerm (permQ n x)), mem_aeModel_ofPerm (permQ_mem_alt x.2)⟩
    with hxτ
  have hp : permQ n (xτ⁻¹ * x : ↥(TL4.aeModel n)) = 1 := by
    push_cast
    rw [map_mul, map_inv, hxτ, permQ_mkQ]
    exact inv_mul_cancel _
  have e : x = xτ * (xτ⁻¹ * x) := by group
  have h1 := permQ_aut_eq_one hn θ hp
  conv_lhs => rw [e]
  rw [map_mul]
  push_cast
  rw [map_mul, h1, mul_one]
  rfl

theorem autAltHom_injective (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) :
    Function.Injective (autAltHom θ) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  have h1 : permQ n (θ ⟨mkQ n (ofPerm τ), mem_aeModel_ofPerm τ.2⟩ : AEQ n) = 1 :=
    congrArg Subtype.val hτ
  have h2 := permQ_aut_eq_one hn θ.symm h1
  rw [MulEquiv.symm_apply_apply] at h2
  apply Subtype.ext
  show (τ : Equiv.Perm (Fin n)) = 1
  have e : permQ n (mkQ n (ofPerm τ)) = τ := rfl
  rw [← e]
  exact h2

@[expose] noncomputable def autAlt (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) :
    MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective (autAltHom θ)
    ⟨autAltHom_injective hn θ, Finite.injective_iff_surjective.mp (autAltHom_injective hn θ)⟩

theorem autAlt_apply (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) (τ : alternatingGroup (Fin n)) :
    autAlt hn θ τ = autAltHom θ τ := rfl

theorem exists_kList_perm : ∀ b : Bool, ∀ d ∈ [d₁, d₂, d₃],
    ∃ k ∈ (bif b then kList else kStarList), k.perm = d := by
  decide

theorem comm_embedPerm_of_cent (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n))
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ τ : alternatingGroup (Fin n),
      (autAlt hn θ τ : Equiv.Perm (Fin n)) = σ * τ * σ⁻¹)
    {β : Finset (Fin n)} {hβ : β.card = 4} {c : Bool}
    (hc : ∀ x (hx : x ∈ memBar β hβ c),
      θ ⟨x, memBar_le_aeModel β hβ c hx⟩ = ⟨x, memBar_le_aeModel β hβ c hx⟩)
    {d : Equiv.Perm (Fin 4)} (hd : d ∈ [d₁, d₂, d₃]) :
    σ * embedPerm (emb β hβ) d = embedPerm (emb β hβ) d * σ := by
  obtain ⟨k, hk, hkd⟩ := exists_kList_perm c d hd
  have hx : mkQ n (embed (emb β hβ) k) ∈ memBar β hβ c := by
    refine ⟨embed (emb β hβ) k, ?_, rfl⟩
    cases c
    · exact ⟨k, hk, rfl⟩
    · exact ⟨k, hk, rfl⟩
  have h1 := hc _ hx
  have h2 := permQ_aut_apply hn θ ⟨_, memBar_le_aeModel β hβ c hx⟩
  rw [h1] at h2
  have h3 : permQ n (mkQ n (embed (emb β hβ) k)) = embedPerm (emb β hβ) d := by
    rw [permQ_mkQ, embed_perm, hkd]
  rw [← autAlt_apply hn θ, hσ] at h2
  change permQ n (mkQ n (embed (emb β hβ) k)) = σ * permQ n (mkQ n (embed (emb β hβ) k)) * σ⁻¹ at h2
  rw [h3] at h2
  calc σ * embedPerm (emb β hβ) d = σ * embedPerm (emb β hβ) d * σ⁻¹ * σ := by group
    _ = embedPerm (emb β hβ) d * σ := by rw [← h2]

theorem exists_conjNormal_six (φ : MulAut (alternatingGroup (Fin 6)))
    (hφ : ∃ k : ℕ, φ ^ 3 ^ k = 1) :
    ∃ σ : Equiv.Perm (Fin 6), MulAut.conjNormal σ = φ := by
  obtain ⟨k, hk⟩ := hφ
  set H := (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
    Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range with hHdef
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  have hH : Nat.card H = 720 := by
    rw [hHdef, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hA := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  have h2 := H.card_mul_index
  rw [hH] at h2
  have hi0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem : φ ∈ H := by
    rcases (show H.index = 1 ∨ H.index = 2 by omega) with h1 | h1
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      exact Subgroup.mem_top φ
    · have : H.Normal := Subgroup.normal_of_index_eq_two h1
      have hsq : φ ^ 2 ∈ H := h1 ▸ Subgroup.pow_index_mem H φ
      obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = 2 * m + 1 := ⟨(3 ^ k - 1) / 2, by
        have : Odd (3 ^ k) := Odd.pow (by decide)
        obtain ⟨r, hr⟩ := this
        omega⟩
      have e : φ = ((φ ^ 2) ^ m)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_mul, ← pow_succ', show 2 * m + 1 = 3 ^ k by omega, hk]
      rw [e]
      exact H.inv_mem (H.pow_mem hsq m)
  obtain ⟨σ, hσ⟩ := hmem
  exact ⟨σ, hσ⟩

theorem exists_conjNormal_of_pow (hn : 5 ≤ n) (φ : MulAut (alternatingGroup (Fin n)))
    (hφ : ∃ k : ℕ, φ ^ 3 ^ k = 1) : ∃ σ : Equiv.Perm (Fin n), MulAut.conjNormal σ = φ := by
  rcases eq_or_ne n 6 with rfl | hn6
  · exact exists_conjNormal_six φ hφ
  · exact (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).2 φ

theorem exists_perm_of_aut (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n))
    (hθ : ∃ k : ℕ, θ ^ 3 ^ k = 1) :
    ∃ σ : Equiv.Perm (Fin n), (∃ k : ℕ, σ ^ 3 ^ k = 1) ∧
      ∀ τ : alternatingGroup (Fin n), (autAlt hn θ τ : Equiv.Perm (Fin n)) = σ * τ * σ⁻¹ := by
  obtain ⟨k, hk⟩ := hθ
  have hpowA : ∀ m : ℕ, ∀ x : ↥(TL4.aeModel n),
      ((autAlt hn θ ^ m) ⟨permQ n x, permQ_mem_alt x.2⟩ : Equiv.Perm (Fin n)) =
        permQ n ((θ ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply]
      have e : (autAlt hn θ ^ m) ⟨permQ n x, permQ_mem_alt x.2⟩ =
          ⟨permQ n ((θ ^ m) x), permQ_mem_alt ((θ ^ m) x).2⟩ := Subtype.ext (ih x)
      rw [e, autAlt_apply, ← permQ_aut_apply hn θ]
  have hAk : autAlt hn θ ^ 3 ^ k = 1 := by
    refine MulEquiv.ext fun τ => Subtype.ext ?_
    have := hpowA (3 ^ k) ⟨mkQ n (ofPerm τ), mem_aeModel_ofPerm τ.2⟩
    rw [hk, MulAut.one_apply] at this
    exact this
  obtain ⟨σ, hσ⟩ := exists_conjNormal_of_pow hn (autAlt hn θ) ⟨k, hAk⟩
  refine ⟨σ, ⟨k, ?_⟩, fun τ => by rw [← hσ, MulAut.conjNormal_apply]⟩
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  rw [map_pow, map_one, hσ, hAk]

theorem fix_of_cent (hn : 5 ≤ n) (θ : MulAut ↥(TL4.aeModel n)) {σ : Equiv.Perm (Fin n)}
    (hσk : ∃ k : ℕ, σ ^ 3 ^ k = 1)
    (hσ : ∀ τ : alternatingGroup (Fin n), (autAlt hn θ τ : Equiv.Perm (Fin n)) = σ * τ * σ⁻¹)
    {β : Finset (Fin n)} {hβ : β.card = 4} {c : Bool}
    (hc : ∀ x (hx : x ∈ memBar β hβ c),
      θ ⟨x, memBar_le_aeModel β hβ c hx⟩ = ⟨x, memBar_le_aeModel β hβ c hx⟩) :
    ∀ x ∈ β, σ x = x := by
  intro x hx
  have hfe := fix_of_comm_embedPerm (emb β hβ) hσk
    (comm_embedPerm_of_cent hn θ hσ hc (by simp))
    (comm_embedPerm_of_cent hn θ hσ hc (by simp))
    (comm_embedPerm_of_cent hn θ hσ hc (by simp))
  have hxr : x ∈ Set.range (emb β hβ) := by rw [range_emb]; exact_mod_cast hx
  obtain ⟨i, rfl⟩ := hxr
  exact hfe i

theorem aut_eq_one_of_cent (hn : 5 ≤ n) (hn7 : n ≠ 7) (θ : MulAut ↥(TL4.aeModel n))
    (hθ : ∃ k : ℕ, θ ^ 3 ^ k = 1) {γ : Finset (Fin n)} (hγ : γ.card = 4) {b₀ : Bool}
    (hcγ : ∀ x (hx : x ∈ memBar γ hγ b₀),
      θ ⟨x, memBar_le_aeModel γ hγ b₀ hx⟩ = ⟨x, memBar_le_aeModel γ hγ b₀ hx⟩)
    (hcβ : ∀ (β : Finset (Fin n)) (hβ : β.card = 4), Disjoint β γ → ∃ c : Bool,
      ∀ x (hx : x ∈ memBar β hβ c),
        θ ⟨x, memBar_le_aeModel β hβ c hx⟩ = ⟨x, memBar_le_aeModel β hβ c hx⟩) : θ = 1 := by
  obtain ⟨σ, hσk, hσ⟩ := exists_perm_of_aut hn θ hθ
  have hσ1 : σ = 1 := perm_eq_one_of_fix hn hn7 hσk hγ (fix_of_cent hn θ hσk hσ hcγ)
    fun β hβ hd => by
      obtain ⟨c, hc⟩ := hcβ β hβ hd
      exact fix_of_cent hn θ hσk hσ hc
  have hperm : ∀ x : ↥(TL4.aeModel n), permQ n (θ x) = permQ n x := by
    intro x
    rw [permQ_aut_apply hn θ, ← autAlt_apply hn θ, hσ, hσ1, one_mul, inv_one, mul_one]
  exact aut_eq_one_of_fix hn θ hθ hperm hγ (hcγ _ (zBar_mem_memBar γ hγ b₀))

end Model

section Transfer

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ}

omit [Finite G] in
theorem AEIdent.center_le_ker (hn : 5 ≤ n) (I : AEIdent P n) :
    Subgroup.center ↥(pSpan P) ≤ I.φ.ker := by
  intro c hc
  have hr : I.φ.range = TL4.aeModel n := I.range_eq
  rw [MonoidHom.mem_ker]
  refine aeModel_center hn _ (by rw [← hr]; exact ⟨c, rfl⟩) fun m' hm' => ?_
  rw [← hr] at hm'
  obtain ⟨x, rfl⟩ := hm'
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc x).symm]

@[expose] def conjSpan {a : G} (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) :
    ↥(pSpan P) →* ↥(pSpan P) where
  toFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem conjSpan_apply {a : G} (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G))
    (x : ↥(pSpan P)) : ((conjSpan ha x : ↥(pSpan P)) : G) = a * x * a⁻¹ := rfl

@[expose] noncomputable def AEIdent.toModel (I : AEIdent P n) : ↥(pSpan P) →* ↥(TL4.aeModel n) :=
  I.φ.codRestrict (TL4.aeModel n) fun x => by
    have hr : I.φ.range = TL4.aeModel n := I.range_eq
    rw [← hr]
    exact ⟨x, rfl⟩

omit [Finite G] in
theorem AEIdent.toModel_surjective (I : AEIdent P n) : Function.Surjective I.toModel := by
  rintro ⟨m, hm⟩
  have hr : I.φ.range = TL4.aeModel n := I.range_eq
  rw [← hr] at hm
  obtain ⟨x, rfl⟩ := hm
  exact ⟨x, rfl⟩

omit [Finite G] in
theorem AEIdent.ker_toModel (I : AEIdent P n) : I.toModel.ker = I.φ.ker := by
  ext x
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact this
  · intro h
    exact Subtype.ext h

omit [Finite G] in
theorem conjSpan_mem_center {a : G} (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G))
    {c : ↥(pSpan P)} (hc : c ∈ Subgroup.center ↥(pSpan P)) :
    conjSpan ha c ∈ Subgroup.center ↥(pSpan P) := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro w
  have hw : a⁻¹ * w * a ∈ pSpan P := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) w).mp w.2
    simpa using this
  have e := congrArg Subtype.val (hc ⟨a⁻¹ * w * a, hw⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul, conjSpan_apply] at e ⊢
  calc (w : G) * (a * c * a⁻¹) = a * ((a⁻¹ * w * a) * c) * a⁻¹ := by group
    _ = a * (c * (a⁻¹ * w * a)) * a⁻¹ := by rw [e]
    _ = a * c * a⁻¹ * w := by group

@[expose] noncomputable def AEIdent.inducedHom (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) :
    ↥(TL4.aeModel n) →* ↥(TL4.aeModel n) :=
  (QuotientGroup.lift I.toModel.ker (I.toModel.comp (conjSpan ha)) (by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, I.ker_toModel]
    rw [I.ker_toModel] at hx
    exact I.center_le_ker hn (conjSpan_mem_center ha (I.ker_le hx)))).comp
    (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm.toMonoidHom

omit [Finite G] in
theorem AEIdent.inducedHom_apply (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) (x : ↥(pSpan P)) :
    I.inducedHom hn ha (I.toModel x) = I.toModel (conjSpan ha x) := by
  simp only [AEIdent.inducedHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have : (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm
      (I.toModel x) = (x : ↥(pSpan P) ⧸ I.toModel.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this, QuotientGroup.lift_mk]
  rfl

omit [Finite G] in
theorem AEIdent.inducedHom_injective (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) :
    Function.Injective (I.inducedHom hn ha) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  obtain ⟨x, rfl⟩ := I.toModel_surjective m
  rw [I.inducedHom_apply hn ha] at hm
  have hk : conjSpan ha x ∈ I.φ.ker := by rw [← I.ker_toModel]; exact hm
  have hc := I.ker_le hk
  have ha' : a⁻¹ ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G) := Subgroup.inv_mem _ ha
  have hc' := conjSpan_mem_center ha' hc
  have e : conjSpan ha' (conjSpan ha x) = x := Subtype.ext (by
    simp only [conjSpan_apply]
    group)
  rw [e] at hc'
  have hx := I.center_le_ker hn hc'
  rw [← I.ker_toModel] at hx
  exact hx

@[expose] noncomputable def AEIdent.inducedAut (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) :
    MulAut ↥(TL4.aeModel n) :=
  MulEquiv.ofBijective (I.inducedHom hn ha)
    ⟨I.inducedHom_injective hn ha,
      Finite.injective_iff_surjective.mp (I.inducedHom_injective hn ha)⟩

omit [Finite G] in
theorem AEIdent.inducedAut_apply (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) (x : ↥(pSpan P)) :
    I.inducedAut hn ha (I.toModel x) = I.toModel (conjSpan ha x) :=
  I.inducedHom_apply hn ha x

omit [Finite G] in
theorem conjSpan_iterate {a : G} (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G))
    (m : ℕ) (x : ↥(pSpan P)) : (((conjSpan ha)^[m] x : ↥(pSpan P)) : G) = a ^ m * x * (a ^ m)⁻¹ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', conjSpan_apply, ih, pow_succ']
    group

omit [Finite G] in
theorem AEIdent.inducedAut_pow_apply (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) (m : ℕ) (x : ↥(pSpan P)) :
    (I.inducedAut hn ha ^ m) (I.toModel x) = I.toModel ((conjSpan ha)^[m] x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply', I.inducedAut_apply hn ha]

omit [Finite G] in
theorem AEIdent.inducedAut_pow_eq_one (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) {m : ℕ} (hm : a ^ m = 1) :
    I.inducedAut hn ha ^ m = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := I.toModel_surjective y
  rw [I.inducedAut_pow_apply hn ha, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [conjSpan_iterate, hm, one_mul, inv_one, mul_one]

omit [Finite G] in
theorem AEIdent.inducedAut_fix_of_comm (hn : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) {M : Subgroup G}
    (hcM : ∀ m ∈ M, a * m = m * a) (x : AE.AEQ n) (hx : x ∈ (M.subgroupOf (pSpan P)).map I.φ)
    (hx' : x ∈ TL4.aeModel n) : I.inducedAut hn ha ⟨x, hx'⟩ = ⟨x, hx'⟩ := by
  obtain ⟨l, hl, rfl⟩ := hx
  have e : (⟨I.φ l, hx'⟩ : ↥(TL4.aeModel n)) = I.toModel l := rfl
  rw [e, I.inducedAut_apply hn ha]
  congr 1
  apply Subtype.ext
  rw [conjSpan_apply, hcM _ (Subgroup.mem_subgroupOf.mp hl), mul_inv_cancel_right]

theorem AEIdent.comm_of_inducedAut_fix {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (h8 : ∀ L ∈ Δ, Nat.card L = 8) (hPΔ : P ⊆ Δ) (hn : 5 ≤ n)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G)) {M : Subgroup G}
    (hM : M ∈ P) (haM : conjSub a M ∈ P)
    (hfix : ∀ x, x ∈ (M.subgroupOf (pSpan P)).map I.φ → ∀ hx' : x ∈ TL4.aeModel n,
      I.inducedAut hn ha ⟨x, hx'⟩ = ⟨x, hx'⟩) :
    ∀ m ∈ M, a * m = m * a := by
  intro m hm
  obtain ⟨β, hβ, c, hlab⟩ := I.label M hM
  have hφ : ∀ x : ↥(pSpan P), (x : G) ∈ M → I.φ (conjSpan ha x) = I.φ x := by
    intro x hxM
    have hx : I.φ x ∈ (M.subgroupOf (pSpan P)).map I.φ :=
      ⟨x, Subgroup.mem_subgroupOf.mpr hxM, rfl⟩
    have := congrArg Subtype.val (hfix _ hx (I.toModel x).2)
    have e : (⟨I.φ x, (I.toModel x).2⟩ : ↥(TL4.aeModel n)) = I.toModel x := rfl
    rw [e, I.inducedAut_apply hn ha] at this
    exact this
  have hle : (M.subgroupOf (pSpan P)).map I.φ ≤ ((conjSub a M).subgroupOf (pSpan P)).map I.φ := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨conjSpan ha l, Subgroup.mem_subgroupOf.mpr ?_, hφ l (Subgroup.mem_subgroupOf.mp hl)⟩
    rw [conjSpan_apply]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hl)
  have heq := TL4.eq_of_map_le_memBar hΩ h2 hn I.φ hk (hPΔ hM) (hPΔ haM) (le_pSpan hM)
    (le_pSpan haM) hlab hle
  have hm' : a * m * a⁻¹ ∈ M := by
    rw [heq]
    exact conj_mem_conjSub hm
  have := phi_injOn I.φ hn hM (h8 M (hPΔ hM)) hlab hm' hm (hφ ⟨m, le_pSpan hM hm⟩ hm)
  calc a * m = a * m * a⁻¹ * a := by group
    _ = m * a := by rw [this]

theorem AEIdent.comm_of_inducedAut_eq_one {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (h8 : ∀ L ∈ Δ, Nat.card L = 8) (hPΔ : P ⊆ Δ) (hn : 5 ≤ n)
    (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {a : G}
    (ha : a ∈ Subgroup.normalizer ((pSpan P : Subgroup G) : Set G))
    (haP : ∀ M ∈ P, conjSub a M ∈ P) (h1 : I.inducedAut hn ha = 1) :
    ∀ x ∈ pSpan P, a * x = x * a := by
  have hle : pSpan P ≤ Subgroup.centralizer ({a} : Set G) := pSpan_le fun M hM y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (I.comm_of_inducedAut_fix hΩ h2 h8 hPΔ hn hk ha hM (haP M hM)
        (fun x _ hx' => by rw [h1]; rfl) y hy).symm
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem ae3Rigid (hn : 5 ≤ n) (hn7 : n ≠ 7) : AE3Rigid n := by
  intro G _ _ Δ hΩ h2 h8 P hPΔ I hk a ha3 haP haN γ hγ M₀ hcent
  classical
  set θ := I.inducedAut hn haN with hθ
  obtain ⟨k, hk3⟩ := ha3
  have hθk : θ ^ 3 ^ k = 1 := I.inducedAut_pow_eq_one hn haN hk3
  have hchoose : ∀ (β : Finset (Fin n)) (hβ : β.card = 4), (β = γ ∨ Disjoint β γ) → ∃ c : Bool,
      ∀ x (hx : x ∈ memBar β hβ c), θ ⟨x, memBar_le_aeModel β hβ c hx⟩ =
        ⟨x, memBar_le_aeModel β hβ c hx⟩ := by
    intro β hβ hβγ
    obtain ⟨Mt, hMt, hlt⟩ := I.label_surj β hβ true
    obtain ⟨Mf, hMf, hlf⟩ := I.label_surj β hβ false
    have hne : Mt ≠ Mf := fun e => AE.memBar_true_ne_false hn β hβ (by rw [← hlt, ← hlf, e])
    by_cases ht : Mt = M₀
    · refine ⟨false, fun x hx => I.inducedAut_fix_of_comm hn haN
        (hcent Mf hMf β hβ false hlf hβγ ?_) x (by rw [hlf]; exact hx) _⟩
      intro e
      exact hne (ht.trans e.symm)
    · exact ⟨true, fun x hx => I.inducedAut_fix_of_comm hn haN
        (hcent Mt hMt β hβ true hlt hβγ ht) x (by rw [hlt]; exact hx) _⟩
  obtain ⟨b₀, hb₀⟩ := hchoose γ hγ (Or.inl rfl)
  have hθ1 : θ = 1 := aut_eq_one_of_cent hn hn7 θ ⟨k, hθk⟩ hγ hb₀
    fun β hβ hd => hchoose β hβ (Or.inr hd)
  exact I.comm_of_inducedAut_eq_one hΩ h2 h8 hPΔ hn hk haN haP hθ1

end Transfer


end CFSG.ClassicalInvolution.Q3.TC.Thin
