module

public import CFSG.Sporadic.Th.Max3.Quotient

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped commutatorElement Matrix

abbrev Vec : Type := Fin 8 → ZMod 2

abbrev Mat8 : Type := Matrix (Fin 8) (Fin 8) (ZMod 2)

theorem vec_add_self (v : Vec) : v + v = 0 := by
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this _

theorem collect_zero_left (c : Fin 8 → Fin 8 → ZMod 2) (w : Vec) :
    CFSG.Certificates.ExtraspecialNF.collect c 0 w = 0 := by
  simp [CFSG.Certificates.ExtraspecialNF.collect]

section Basic


theorem nf_zero_zero : nf 0 0 = 1 := CFSG.Certificates.ExtraspecialNF.nf_zero_zero z q

theorem nf_zero_vec (b : ZMod 2) : nf b 0 = z ^ b.val :=
  CFSG.Certificates.ExtraspecialNF.nf_zero_vec z q b

theorem nf_single (j : Fin 8) : nf 0 (Pi.single j 1) = q j :=
  CFSG.Certificates.ExtraspecialNF.nf_single z q j

theorem nf_eq_zpow_mul (s : ZMod 2) (v : Vec) : nf s v = z ^ s.val * nf 0 v := by
  simp [nf]

end Basic

section Action


open scoped Classical in
@[expose] noncomputable def vecPart (g : J) : Vec :=
  if h : g ∈ Q then Classical.choose (Classical.choose_spec (mem_Q_iff.1 h)) else 0

theorem vecPart_eq {g : J} {s : ZMod 2} {v : Vec} (h : nf s v = g) : vecPart g = v := by
  have hg : g ∈ Q := h ▸ nf_mem_Q s v
  unfold vecPart
  rw [dite_eq_left hg]
  have hs := Classical.choose_spec (Classical.choose_spec (mem_Q_iff.1 hg))
  exact congrArg Prod.snd (nf_injective
    (a₁ := (Classical.choose (mem_Q_iff.1 hg), Classical.choose (Classical.choose_spec
      (mem_Q_iff.1 hg)))) (a₂ := (s, v)) (hs.trans h.symm))

theorem vecPart_nf (s : ZMod 2) (v : Vec) : vecPart (nf s v) = v := vecPart_eq (Eq.refl (nf s v))

@[expose] noncomputable def rho (g : J) : Mat8 := Matrix.of fun k i => vecPart (g * q i * g⁻¹) k

theorem rho_apply (g : J) (k i : Fin 8) : rho g k i = vecPart (g * q i * g⁻¹) k := rfl

theorem nf_mul (s t : ZMod 2) (v w : Vec) :
    nf s v * nf t w = nf (s + t + CFSG.Certificates.ExtraspecialNF.collect c v w) (v + w) :=
  CFSG.Certificates.ExtraspecialNF.nf_mul_nf symplectic_rel s t v w

theorem zpow_mul_nf (b t : ZMod 2) (w : Vec) : z ^ b.val * nf t w = nf (b + t) w := by
  rw [← nf_zero_vec, nf_mul, collect_zero_left, add_zero, zero_add]

theorem inv_nf (s : ZMod 2) (v : Vec) :
    (nf s v)⁻¹ = nf (s + CFSG.Certificates.ExtraspecialNF.collect c v v) v := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [nf_mul]
  have e1 : ∀ a b : ZMod 2, a + (a + b) + b = 0 := by decide
  have e2 : v + v = 0 := by
    funext i
    have : ∀ a : ZMod 2, a + a = 0 := by decide
    exact this _
  rw [e1, e2, nf_zero_zero]

theorem conj_nf {g : J} (hg : g ∈ M) (s : ZMod 2) (v : Vec) :
    ∃ t, g * nf s v * g⁻¹ = nf t (rho g *ᵥ v) := by
  have h : ∀ i, ∃ a b, nf a b = g * q i * g⁻¹ := fun i =>
    mem_Q_iff.1 (AltQuot.conj_mem_Q_of_mem_M hg (q_mem_Q i))
  choose a b hab using h
  have hb : ∀ i, vecPart (g * q i * g⁻¹) = b i := fun i => vecPart_eq (hab i)
  obtain ⟨t, ht⟩ := conj_nf_zero g a b (fun i => (hab i).symm) v
  have hv : rho g *ᵥ v = fun k => ∑ i, v i * b i k := by
    funext k
    simp [rho, Matrix.mulVec, dotProduct, hb, mul_comm]
  rw [hv]
  refine ⟨s + t, ?_⟩
  rw [nf_eq_zpow_mul s v, ← zpow_mul_nf s t]
  have hc : g * z ^ s.val = z ^ s.val * g := by
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases s with rfl | rfl
    · simp
    · rw [CFSG.Certificates.ExtraspecialNF.val_one_two, pow_one]
      exact (commute_z_of_mem_M hg).symm.eq
  calc g * (z ^ s.val * nf 0 v) * g⁻¹ = z ^ s.val * (g * nf 0 v * g⁻¹) := by
        rw [← mul_assoc, ← mul_assoc, hc]
        simp only [mul_assoc]
    _ = z ^ s.val * nf t fun k => ∑ i, v i * b i k := by rw [ht]

theorem rho_one : rho 1 = 1 := by
  ext k i
  rw [rho_apply, one_mul, inv_one, mul_one, ← nf_single i, vecPart_nf, Matrix.one_apply,
    Pi.single_apply]

theorem rho_mul {g h : J} (hg : g ∈ M) (hh : h ∈ M) : rho (g * h) = rho g * rho h := by
  ext k i
  obtain ⟨s, hs⟩ : ∃ s, nf s (fun j => rho h j i) = h * q i * h⁻¹ := by
    obtain ⟨s, w, hw⟩ := mem_Q_iff.1 (AltQuot.conj_mem_Q_of_mem_M hh (q_mem_Q i))
    have : vecPart (h * q i * h⁻¹) = w := vecPart_eq hw
    refine ⟨s, ?_⟩
    have e : (fun j => rho h j i) = w := by
      funext j
      rw [rho_apply, this]
    rw [e, hw]
  obtain ⟨t, ht⟩ := conj_nf hg s (fun j => rho h j i)
  have e : g * h * q i * (g * h)⁻¹ = g * (h * q i * h⁻¹) * g⁻¹ := by group
  rw [rho_apply, e, ← hs, ht, vecPart_nf, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct]

theorem rho_x : rho x = B1 := by
  ext k i
  rw [rho_apply, x_conj_q, vecPart_nf]
  rfl

theorem rho_y : rho y = B2 := by
  ext k i
  rw [rho_apply, y_conj_q, vecPart_nf]
  rfl

theorem comm_nf {g : J} (hg : g ∈ M) (s : ZMod 2) (v : Vec) :
    ∃ t, ⁅g, nf s v⁆ = nf t ((rho g + 1) *ᵥ v) := by
  obtain ⟨t, ht⟩ := conj_nf hg s v
  refine ⟨t + (s + CFSG.Certificates.ExtraspecialNF.collect c v v) +
    CFSG.Certificates.ExtraspecialNF.collect c (rho g *ᵥ v) v, ?_⟩
  rw [commutatorElement_def, ht, inv_nf, nf_mul, Matrix.add_mulVec, Matrix.one_mulVec]

theorem comm_nf' {g : J} (hg : g ∈ M) (s : ZMod 2) (v : Vec) :
    ∃ t, ⁅nf s v, g⁆ = nf t ((rho g + 1) *ᵥ v) := by
  obtain ⟨t, ht⟩ := comm_nf hg s v
  refine ⟨t + CFSG.Certificates.ExtraspecialNF.collect c ((rho g + 1) *ᵥ v) ((rho g + 1) *ᵥ v),
    ?_⟩
  rw [← commutatorElement_inv, ht, inv_nf]

theorem rho_eq_one_iff {m : J} (hm : m ∈ M) :
    rho m = 1 ↔ m ∈ Q := by
  constructor
  · intro h
    refine (mem_Q_iff_comm_mem_zpowers hm).2 fun g hg => ?_
    obtain ⟨s, v, rfl⟩ := mem_Q_iff.1 hg
    obtain ⟨t, ht⟩ := comm_nf hm s v
    rw [ht, h, Matrix.add_mulVec, Matrix.one_mulVec, vec_add_self, nf_zero_vec]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
  · intro hQ
    ext k i
    obtain ⟨b, hb⟩ := (CFSG.Certificates.ExtraspecialNF.mem_zpowers_iff_exists
      symplectic_rel).1 (AltQuot.comm_mem_zpowers hQ (q_mem_Q i))
    have e : m * q i * m⁻¹ = nf b (Pi.single i 1) := by
      have h1 : m * q i * m⁻¹ = ⁅m, q i⁆ * q i := by
        simp only [commutatorElement_def]
        group
      rw [h1, ← hb, ← nf_single i, zpow_mul_nf, add_zero]
    rw [rho_apply, e, vecPart_nf, Matrix.one_apply, Pi.single_apply]

theorem rho_wordProd (w : List Gen) : rho (wordProd w) = (w.map (Gen.eval B1 B2)).prod := by
  induction w with
  | nil => simpa [wordProd] using rho_one
  | cons l w ih =>
    have e : wordProd (l :: w) = Gen.eval x y l * wordProd w := by simp [wordProd]
    have hl : Gen.eval x y l ∈ M := by cases l <;> simp [Gen.eval, x_mem_M, y_mem_M]
    rw [e, rho_mul hl (wordProd_mem_M w), ih, List.map_cons, List.prod_cons]
    cases l
    · show rho x * _ = B1 * _
      rw [rho_x]
    · show rho y * _ = B2 * _
      rw [rho_y]

end Action

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
