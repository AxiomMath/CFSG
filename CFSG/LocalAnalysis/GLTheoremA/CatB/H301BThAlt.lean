module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalMax
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open Equiv CFSG.Open CFSG.AGLEmbedding.A9Local CFSG.AGLEmbedding.A9Local.NrmMax

@[expose] def ninePtEquiv : Fin 9 ≃ Pt := (finProdFinEquiv (m := 3) (n := 3)).symm

@[expose] def nineCyc (k : ZMod 3) : Perm (Fin 9) :=
  ninePtEquiv.permCongrHom.symm (shiftPerm (Pi.single k 1))

@[expose] def nineExp (u : ZMod 3 × ZMod 3 × ZMod 3) : Perm (Fin 9) :=
  nineCyc 0 ^ u.1.val * nineCyc 1 ^ u.2.1.val * nineCyc 2 ^ u.2.2.val

@[expose] def baseNine : Subgroup (Perm (Fin 9)) :=
  baseGroup.map ninePtEquiv.permCongrHom.symm.toMonoidHom

private theorem shiftPerm_single_pow : ∀ k t : ZMod 3,
    shiftPerm (Pi.single k t) = shiftPerm (Pi.single k 1) ^ t.val := by
  decide +kernel

private theorem shiftPerm_eq_prod (f : ZMod 3 → ZMod 3) :
    shiftPerm f = shiftPerm (Pi.single 0 1) ^ (f 0).val * shiftPerm (Pi.single 1 1) ^ (f 1).val *
      shiftPerm (Pi.single 2 1) ^ (f 2).val := by
  have hf : f = Pi.single 0 (f 0) + Pi.single 1 (f 1) + Pi.single 2 (f 2) := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hi with rfl | rfl | rfl <;> simp +decide [Pi.single_apply]
  rw [← shiftPerm_single_pow, ← shiftPerm_single_pow, ← shiftPerm_single_pow, ← shiftPerm_add,
    ← shiftPerm_add, ← hf]

theorem mem_baseNine_iff {σ : Perm (Fin 9)} : σ ∈ baseNine ↔ ∃ u, σ = nineExp u := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨f, rfl⟩ := mem_baseGroup_iff.1 hτ
    refine ⟨(f 0, f 1, f 2), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, nineExp, nineCyc]
    rw [shiftPerm_eq_prod f, map_mul, map_mul, map_pow, map_pow, map_pow]
  · rintro ⟨u, rfl⟩
    have hc : ∀ k, nineCyc k ∈ baseNine := fun k => by
      rw [baseNine]
      exact Subgroup.mem_map.2 ⟨_, shiftPerm_mem_baseGroup _, rfl⟩
    exact baseNine.mul_mem (baseNine.mul_mem (baseNine.pow_mem (hc 0) _)
      (baseNine.pow_mem (hc 1) _)) (baseNine.pow_mem (hc 2) _)

theorem nineExp_zero : nineExp 0 = 1 := by decide +kernel

theorem nineExp_add_self : ∀ u, nineExp (u + u) = nineExp u * nineExp u := by decide +kernel

private theorem map_symm_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) :
    (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  ext x
  simp

private theorem map_conj_inv_map_conj {G : Type*} [Group G] (K : Subgroup G) (h : G) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = K := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_of_mem_normalizer {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.1 hg _).2 ?_, by group⟩
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]

private theorem map_conj_mul {G : Type*} [Group G] (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_map_conj_eq {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (h : G)
    (K : Subgroup G) : (K.map ψ.toMonoidHom).map (MulAut.conj (ψ h)).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).map ψ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem map_baseNine : baseNine.map ninePtEquiv.permCongrHom.toMonoidHom = baseGroup := by
  have h := map_symm_map ninePtEquiv.permCongrHom.symm baseGroup
  rwa [MulEquiv.symm_symm] at h

theorem exists_conj_eq_baseNine {E : Subgroup (Perm (Fin 9))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 27) :
    ∃ g ∈ alternatingGroup (Fin 9), E = baseNine.map (MulAut.conj g).toMonoidHom := by
  set φ := ninePtEquiv.permCongrHom with hφ
  have hc' : Nat.card (E.map φ.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
    norm_num
  obtain ⟨g', hg'⟩ := exists_conj_eq_baseGroup (hE.map φ.toMonoidHom) hc'
  obtain ⟨g, hgs, hg⟩ : ∃ g : Perm Pt, Perm.sign g = 1 ∧
      (E.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom = baseGroup := by
    rcases Int.units_eq_one_or (Perm.sign g') with hs | hs
    · exact ⟨g', hs, hg'⟩
    · refine ⟨negAll * g', by rw [Perm.sign_mul, sign_negAll, hs]; decide, ?_⟩
      rw [map_conj_mul, hg']
      exact map_conj_of_mem_normalizer negAll_mem_nrm
  refine ⟨φ.symm g⁻¹, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, hφ, Equiv.permCongrHom_symm, Equiv.permCongrHom_coe,
      Perm.sign_permCongr, Perm.sign_inv, hgs]
  · rw [baseNine, ← hφ, map_map_conj_eq, ← hg, map_conj_inv_map_conj, map_symm_map]

private theorem zmod_three_cover : ∀ z w u : ZMod 3, z ≠ w → u = z ∨ u = w ∨ u = w + (w - z) := by
  decide

private theorem eq_bot_of_baseGroup_le_normalizer {X : Subgroup (Perm Pt)} (hX : IsPGroup 2 X)
    (hB : baseGroup ≤ Subgroup.normalizer (X : Set (Perm Pt))) : X = ⊥ := by
  have hconj : ∀ (f : ZMod 3 → ZMod 3) (g : Perm Pt), g ∈ X →
      shiftPerm f * g * (shiftPerm f)⁻¹ ∈ X := fun f g hg =>
    (Subgroup.mem_normalizer_iff.1 (hB (shiftPerm_mem_baseGroup f)) g).1 hg
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ p := by
    by_contra h
    push Not at h
    exact hx1 (Equiv.ext h)
  set O : Set Pt := {q | ∃ g ∈ X, g p = q} with hO
  have hpO : p ∈ O := ⟨1, X.one_mem, rfl⟩
  have hact : ∀ q ∈ O, ∀ g ∈ X, g q ∈ O := by
    rintro q ⟨h, hh, rfl⟩ g hg
    exact ⟨g * h, X.mul_mem hg hh, rfl⟩
  have hfix : ∀ (f : ZMod 3 → ZMod 3) (r : Pt), r ∈ O → shiftPerm f r = r →
      ∀ q ∈ O, shiftPerm f q ∈ O := by
    rintro f r ⟨h, hh, rfl⟩ hr q ⟨k, hk, rfl⟩
    have e : shiftPerm f (k p) =
        (shiftPerm f * (k * h⁻¹) * (shiftPerm f)⁻¹) (shiftPerm f (h p)) := by
      simp [Perm.mul_apply]
    rw [e, hr]
    exact hact _ ⟨h, hh, rfl⟩ _ (hconj f _ (X.mul_mem hk (X.inv_mem hh)))
  have hvert : ∀ q ∈ O, ∀ t : ZMod 3, (q.1, q.2 + t) ∈ O := by
    intro q hq t
    by_cases hr : ∃ r ∈ O, r.1 ≠ q.1
    · obtain ⟨r, hrO, hr1⟩ := hr
      have h := hfix (Pi.single q.1 t) r hrO (by simp [Pi.single_apply, hr1]) q hq
      simpa using h
    · push Not at hr
      have hxO : x p ∈ O := ⟨x, hx, rfl⟩
      have h1 : (x p).1 = q.1 := hr _ hxO
      have h0 : p.1 = q.1 := hr _ hpO
      have hne : p.2 ≠ (x p).2 := fun h => hp (Prod.ext (h1.trans h0.symm) h.symm)
      set σ := shiftPerm (Pi.single q.1 ((x p).2 - p.2)) with hσ
      have hσp : σ p = x p := by
        rw [hσ, shiftPerm_apply, h0]
        exact Prod.ext h1.symm (by simp only [Pi.single_eq_same]; ring)
      have h3 : σ (x p) ∈ O := by
        have e : σ (x p) = (σ * x * σ⁻¹) (σ p) := by simp [Perm.mul_apply]
        rw [e, hσp]
        exact hact _ hxO _ (hconj _ _ hx)
      have h3' : σ (x p) = (q.1, (x p).2 + ((x p).2 - p.2)) := by
        rw [hσ, shiftPerm_apply, h1]
        simp
      rcases zmod_three_cover p.2 (x p).2 (q.2 + t) hne with h | h | h
      · rw [h, ← h0]
        exact hpO
      · rw [h, ← h1]
        exact hxO
      · rw [h, ← h3']
        exact h3
  have hprod : O = (Prod.fst '' O) ×ˢ Set.univ := by
    ext q
    simp only [Set.mem_prod, Set.mem_image, Set.mem_univ, and_true]
    constructor
    · intro hq
      exact ⟨q, hq, rfl⟩
    · rintro ⟨r, hr, hrq⟩
      have h := hvert r hr (q.2 - r.2)
      rwa [show (r.1, r.2 + (q.2 - r.2)) = q from Prod.ext hrq (by ring)] at h
  have horb : MulAction.orbit X p = O := by
    ext q
    simp only [MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mk_smul, Perm.smul_def, hO,
      Set.mem_setOf_eq, exists_prop]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.card_orbit p
  rw [horb, Nat.card_coe_set_eq, hprod, Set.ncard_prod, Set.ncard_univ, Nat.card_zmod] at hn
  have h3 : 3 ∣ 2 ^ n := Dvd.intro_left _ hn
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem eq_bot_of_elemAbelian27_le_normalizer {E X : Subgroup (Perm (Fin 9))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) (hX : IsPGroup 2 X)
    (hEX : E ≤ Subgroup.normalizer (X : Set (Perm (Fin 9)))) : X = ⊥ := by
  obtain ⟨g, -, rfl⟩ := exists_conj_eq_baseNine hE hc
  set ψ : Perm (Fin 9) →* Perm Pt :=
    ninePtEquiv.permCongrHom.toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom with hψ
  have hinj : Function.Injective ψ :=
    ninePtEquiv.permCongrHom.injective.comp (MulAut.conj g⁻¹).injective
  have h1 : (baseNine.map (MulAut.conj g).toMonoidHom).map ψ = baseGroup := by
    rw [hψ, ← Subgroup.map_map, map_conj_inv_map_conj, map_baseNine]
  have hN : baseGroup ≤ Subgroup.normalizer ((X.map ψ : Subgroup (Perm Pt)) : Set (Perm Pt)) := by
    rw [← h1]
    exact (Subgroup.map_mono hEX).trans (Subgroup.le_normalizer_map ψ)
  exact (Subgroup.map_eq_bot_iff_of_injective X hinj).1
    (eq_bot_of_baseGroup_le_normalizer (hX.map ψ) hN)

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
