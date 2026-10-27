module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc2

public section

namespace CFSG.QuasithinUnique.A5.Kc3Cert

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

section Props2

variable {n : ℕ}

@[expose] def ECert.hypDCheck (gR : List (RN n)) (c : ECert) : Bool :=
  c.selfCentCheck gR && (c.nOrd % 3840 == 0)

@[expose] def ECert.hypVCheck (gR : List (RN n)) (c : ECert) (omW : List ℕ) : Bool :=
  let ω := evalW gR omW
  let El := (c.Es gR).toList
  let Ns := c.Ns gR
  Ns.contains ω && El.any (fun v => ω * v != v * ω) &&
    El.all (fun v => ω * ω * ω * v == v * (ω * ω * ω)) &&
    Ns.toList.all fun x =>
      let A := x * ω
      let B := ω * x
      let C := ω * ω * x
      let eB := El.map fun e => (e * A, e * B)
      let eC := El.map fun e => (e * A, e * C)
      (El.all fun v => eB.any fun p => A * v == p.1 && B * v == p.2) ||
        (El.all fun v => eC.any fun p => A * v == p.1 && C * v == p.2)

variable {G : Type} [Group G] {enc : G → RN n} {a b : G} {c : ECert} {E N : Subgroup G}

theorem ECert.Sound.hypD (h : IsEnc enc) (hs : c.Sound enc a b E N)
    (hck : c.hypDCheck ([a, b, a⁻¹, b⁻¹].map enc) = true) : LocHypD E := by
  simp only [ECert.hypDCheck, Bool.and_eq_true, beq_iff_eq] at hck
  obtain ⟨hsc, h3840⟩ := hck
  refine ⟨hs.centralizer_le h hsc, ?_⟩
  rw [← hs.hN, hs.cardN]
  exact Nat.dvd_of_mod_eq_zero h3840

theorem pow3_comm {R : Type*} [Mul R] (enc : G → R) (hinj : Function.Injective enc)
    (hmul : ∀ x y, enc (x * y) = enc x * enc y) (ω v : G)
    (h : enc ω * enc ω * enc ω * enc v = enc v * (enc ω * enc ω * enc ω)) :
    ω ^ 3 * v = v * ω ^ 3 := by
  apply hinj
  have e1 : ω ^ 3 = ω * ω * ω := pow_three' ω
  simp only [e1, hmul]
  exact h

theorem conj_eq_of_comm {x v e : G} (h : x * v = e * x) : x * v * x⁻¹ = e := by
  rw [h]; group

theorem hypV_step {R : Type*} [Mul R] (enc : G → R) (hinj : Function.Injective enc)
    (hmul : ∀ x y, enc (x * y) = enc x * enc y) (m ω v e : G)
    (h1 : enc m * enc ω * enc v = enc e * (enc m * enc ω))
    (h2 : enc ω * enc m * enc v = enc e * (enc ω * enc m)) :
    m * ω * v * ω⁻¹ * m⁻¹ = ω * m * v * m⁻¹ * ω⁻¹ := by
  have a1 : (m * ω) * v = e * (m * ω) := hinj (by simp only [hmul]; exact h1)
  have a2 : (ω * m) * v = e * (ω * m) := hinj (by simp only [hmul]; exact h2)
  have b1 := conj_eq_of_comm a1
  have b2 := conj_eq_of_comm a2
  calc m * ω * v * ω⁻¹ * m⁻¹ = (m * ω) * v * (m * ω)⁻¹ := by group
    _ = e := b1
    _ = (ω * m) * v * (ω * m)⁻¹ := b2.symm
    _ = ω * m * v * m⁻¹ * ω⁻¹ := by group

theorem hypV_step2 {R : Type*} [Mul R] (enc : G → R) (hinj : Function.Injective enc)
    (hmul : ∀ x y, enc (x * y) = enc x * enc y) (m ω v e : G)
    (h1 : enc m * enc ω * enc v = enc e * (enc m * enc ω))
    (h2 : enc ω * enc ω * enc m * enc v = enc e * (enc ω * enc ω * enc m)) :
    m * ω * v * ω⁻¹ * m⁻¹ = ω * ω * m * v * m⁻¹ * ω⁻¹ * ω⁻¹ := by
  have a1 : (m * ω) * v = e * (m * ω) := hinj (by simp only [hmul]; exact h1)
  have a2 : (ω * ω * m) * v = e * (ω * ω * m) := hinj (by simp only [hmul]; exact h2)
  have b1 := conj_eq_of_comm a1
  have b2 := conj_eq_of_comm a2
  calc m * ω * v * ω⁻¹ * m⁻¹ = (m * ω) * v * (m * ω)⁻¹ := by group
    _ = e := b1
    _ = (ω * ω * m) * v * (ω * ω * m)⁻¹ := b2.symm
    _ = ω * ω * m * v * m⁻¹ * ω⁻¹ * ω⁻¹ := by group

theorem ECert.Sound.hypV (h : IsEnc enc) (hs : c.Sound enc a b E N) (omW : List ℕ)
    (hck : c.hypVCheck ([a, b, a⁻¹, b⁻¹].map enc) omW = true) : LocHypV E := by
  set gl : List G := [a, b, a⁻¹, b⁻¹] with hgl
  set ω : G := evalW gl omW with hω
  have hencω : enc ω = evalW (gl.map enc) omW := enc_evalW h gl omW
  simp only [ECert.hypVCheck, Bool.and_eq_true, Std.HashSet.contains_iff_mem, List.any_eq_true,
    List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at hck
  obtain ⟨⟨⟨hωN, hωmove⟩, hω3⟩, hnorm⟩ := hck
  rw [← hencω] at hωN hωmove hω3 hnorm
  have hωN' : ω ∈ Subgroup.normalizer (E : Set G) := by
    rw [← hs.hN]
    exact (hs.memN ω).2 hωN
  refine ⟨ω, hωN', ?_, ?_, ?_⟩
  · obtain ⟨v', hv', hne⟩ := hωmove
    obtain ⟨v, hv, rfl⟩ := hs.surjE v' (Std.HashSet.mem_toList.1 hv')
    refine ⟨v, hv, fun heq => hne ?_⟩
    rw [← h.map_mul, ← h.map_mul, heq]
  · intro v hv
    have := hω3 (enc v) (Std.HashSet.mem_toList.2 ((hs.memE v).1 hv))
    exact pow3_comm enc h.inj h.map_mul ω v this
  · intro m hm
    have hmN : m ∈ N := by rw [hs.hN]; exact hm
    rcases hnorm (enc m) (Std.HashSet.mem_toList.2 ((hs.memN m).1 hmN)) with h1 | h1
    · left
      intro v hv
      obtain ⟨p, hp, hA, hB⟩ := h1 (enc v) (Std.HashSet.mem_toList.2 ((hs.memE v).1 hv))
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
      obtain ⟨e', he', rfl⟩ := hs.surjE e (Std.HashSet.mem_toList.1 he)
      exact hypV_step enc h.inj h.map_mul m ω v e' hA hB
    · right
      intro v hv
      obtain ⟨p, hp, hA, hB⟩ := h1 (enc v) (Std.HashSet.mem_toList.2 ((hs.memE v).1 hv))
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
      obtain ⟨e', he', rfl⟩ := hs.surjE e (Std.HashSet.mem_toList.1 he)
      exact hypV_step2 enc h.inj h.map_mul m ω v e' hA hB

end Props2

end CFSG.QuasithinUnique.A5.Kc3Cert
