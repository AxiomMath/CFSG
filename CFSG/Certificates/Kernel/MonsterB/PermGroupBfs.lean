module

public import CFSG.Certificates.Kernel.MonsterB.PermBfsSound
public import CFSG.Quasithin.Recognition.CertChain
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

@[expose] def encP (g : Equiv.Perm (Fin 24)) : Array ℕ := Array.ofFn fun i => (g i : ℕ)

theorem encP_getElem (g : Equiv.Perm (Fin 24)) (i : Fin 24) : (encP g)[(i : ℕ)]! = g i := by
  rw [encP, getElem!_pos _ _ (by simp), Array.getElem_ofFn]

theorem PermArr_encP (g : Equiv.Perm (Fin 24)) : PermArr (encP g) = true := by
  simp only [PermArr, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨by simp [encP], fun i hi => ?_⟩, fun j hj => ?_⟩
  · rw [encP_getElem g ⟨i, hi⟩]
    exact (g ⟨i, hi⟩).2
  · obtain ⟨i, e⟩ := g.surjective ⟨j, hj⟩
    exact ⟨i, i.2, by rw [encP_getElem g i, e]⟩

theorem decode_encP (g : Equiv.Perm (Fin 24)) : decode (encP g) = g := by
  ext i
  rw [decode_apply (PermArr_encP g), encP_getElem]

theorem encP_decode {a : Array ℕ} (h : PermArr a = true) : encP (decode a) = a :=
  decode_inj (PermArr_encP _) h (decode_encP _)

@[expose] noncomputable def genH (gens : Array (Array ℕ)) : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure ((fun k => decode gens[k]!) '' {k | k < gens.size})

theorem reach_amul_iff {gens : Array (Array ℕ)} (hg : ∀ k < gens.size, PermArr gens[k]! = true)
    (x : Array ℕ) :
    Reach (fun k x => amul gens[k]! x) gens.size idArr x ↔
      PermArr x = true ∧ decode x ∈ genH gens := by
  constructor
  · intro h
    induction h with
    | root => exact ⟨PermArr_idArr, by rw [decode_idArr]; exact one_mem _⟩
    | step k hk _ ih =>
      refine ⟨PermArr_amul (hg k hk) ih.1, ?_⟩
      rw [decode_amul (hg k hk) ih.1]
      exact mul_mem (Subgroup.subset_closure ⟨k, hk, rfl⟩) ih.2
  · rintro ⟨hx, hm⟩
    let F : Set (Equiv.Perm (Fin 24)) :=
      {g | Reach (fun k x => amul gens[k]! x) gens.size idArr (encP g)}
    have hF : ∀ s ∈ (fun k => decode gens[k]!) '' {k | k < gens.size}, ∀ g ∈ F, s • g ∈ F := by
      rintro s ⟨k, hk, rfl⟩ g hgF
      change Reach _ _ _ (encP (decode gens[k]! * g))
      have e : encP (decode gens[k]! * g) = amul gens[k]! (encP g) := by
        rw [← decode_encP g, ← decode_amul (hg k hk) (PermArr_encP g), decode_encP,
          encP_decode (PermArr_amul (hg k hk) (PermArr_encP g))]
      rw [e]
      exact Reach.step k hk hgF
    have h1 : (1 : Equiv.Perm (Fin 24)) ∈ F := by
      change Reach _ _ _ (encP 1)
      rw [← decode_idArr, encP_decode PermArr_idArr]
      exact Reach.root
    have := CFSG.Perm.smul_mem_of_finite_of_mem_closure (Set.toFinite F) hF hm h1
    rw [smul_eq_mul, mul_one] at this
    change Reach _ _ _ (encP (decode x)) at this
    rwa [encP_decode hx] at this

theorem bfsCert_amul_card {gens : Array (Array ℕ)} (hg : ∀ k < gens.size, PermArr gens[k]! = true)
    {fuel : ℕ} (hf : Nat.card (genH gens) ≤ fuel) :
    certOK amul gens idArr (bfsCert amul gens idArr fuel) = true ∧
      (bfsCert amul gens idArr fuel).pts.size = Nat.card (genH gens) := by
  classical
  let S : Finset (Array ℕ) :=
    (Set.toFinite (genH gens : Set (Equiv.Perm (Fin 24)))).toFinset.image encP
  have hinj : Function.Injective encP := fun a b e => by
    rw [← decode_encP a, ← decode_encP b, e]
  have hcard : S.card = Nat.card (genH gens) := by
    rw [Finset.card_image_of_injective _ hinj, ← Nat.card_eq_card_finite_toFinset]
    rfl
  have hS : ∀ x, Reach (fun k x => amul gens[k]! x) gens.size idArr x ↔ x ∈ S := by
    intro x
    rw [reach_amul_iff hg]
    simp only [S, Finset.mem_image, Set.Finite.mem_toFinset, SetLike.mem_coe]
    constructor
    · rintro ⟨hx, hm⟩
      exact ⟨_, hm, encP_decode hx⟩
    · rintro ⟨g, hm, rfl⟩
      exact ⟨PermArr_encP g, by rwa [decode_encP]⟩
  have hv : ∀ x ∈ S, PermArr x = true := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    exact PermArr_encP g
  obtain ⟨h1, -, h3, -⟩ := bfsCert_spec (fuel := fuel) S hS hv (by rw [hcard]; exact hf)
  exact ⟨h1, h3.trans hcard⟩

theorem decode_eq_permOfArr {a : Array ℕ} (h : PermArr a = true) :
    decode a = CFSG.Monster.B.Co2.permOfArr 24 a := by
  have hc : (∀ i < 24, a[i]! < 24) ∧ ∀ i < 24, ∀ j < 24, a[i]! = a[j]! → i = j := by
    refine ⟨fun i hi => PermArr_lt h ⟨i, hi⟩, fun i hi j hj e => ?_⟩
    have e' : decode a ⟨i, hi⟩ = decode a ⟨j, hj⟩ := Fin.ext (by
      rw [decode_apply h, decode_apply h]
      exact e)
    exact congrArg Fin.val ((decode a).injective e')
  ext i
  rw [decode_apply h, CFSG.Monster.B.Co2.permOfArr, dite_eq_left hc]
  rfl

theorem card_genH_of_rawChainOK {gens S : Array (Array ℕ)}
    (hg : ∀ k < gens.size, PermArr gens[k]! = true) {W : Array (List ℤ)} {base : List (Fin 24)}
    (hb : base.Nodup) (hOS : gens.size ≤ S.size) (hSO : ∀ i < gens.size, S[i]! = gens[i]!)
    (h : CFSG.Certificates.Native.rawChainOK 24 (S.extract 0 gens.size) S
      (base.map Fin.val).toArray W 1 = true) :
    Nat.card (genH gens) =
      (CFSG.Certificates.Native.rawOrbitSizes 24 S (base.map Fin.val).toArray).prod := by
  have e : (fun k => decode gens[k]!) '' {k | k < gens.size} =
      {g | ∃ k < gens.size, CFSG.Monster.B.Co2.permOfArr 24 gens[k]! = g} := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, (decode_eq_permOfArr (hg k hk)).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, decode_eq_permOfArr (hg k hk)⟩
  rw [genH, e]
  exact CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (by norm_num) hb (by norm_num) hOS
    hSO h

end CFSG.KC.Bfs

end
