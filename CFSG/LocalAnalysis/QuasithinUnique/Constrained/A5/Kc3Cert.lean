module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.QuasithinUnique.A5.Kc3Cert

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

section Pure

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_conj_le {E : Subgroup G} {g : G} (h : ∀ x ∈ E, g * x * g⁻¹ ∈ E) :
    g ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : E → E := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hf : Function.Injective f := by
    intro y z hyz
    have h1 : g * (y : G) * g⁻¹ = g * (z : G) * g⁻¹ := congrArg Subtype.val hyz
    exact Subtype.ext (by simpa using h1)
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hf ⟨g * x * g⁻¹, hx⟩
  have h2 : g * (y : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hy
  have h3 : (y : G) = x := by simpa using h2
  rw [← h3]
  exact y.2

omit [Finite G] in
theorem closure_comm {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hS y hy x hx)
  intro x hx y hy
  have h2 : ∀ z ∈ S, z * x = x * z := fun z hz => Subgroup.mem_centralizer_iff.1 (h1 hx) z hz
  have h3 : Subgroup.closure S ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    exact (h2 z hz).symm
  exact Subgroup.mem_centralizer_iff.1 (h3 hy) x rfl

end Pure

structure ECert where
  eW : List (List ℕ)
  nW : List (List ℕ)
  nOrd : ℕ
  depth : ℕ
  rT : List ℕ

section Check

variable {n : ℕ} (gR : List (RN n)) (c : ECert)

@[expose] def ECert.eR : List (RN n) := c.eW.map (evalW gR)

@[expose] def ECert.nR : List (RN n) := c.nW.map (evalW gR)

@[expose] def ECert.Es : Std.HashSet (RN n) := bfsSet (c.eR gR) 16

@[expose] def ECert.Ns : Std.HashSet (RN n) := bfsSet (c.nR gR) c.depth

@[expose] def ECert.eCheck : Bool :=
  let Es := c.Es gR
  closedH (c.eR gR) Es && Es.size == 16 && (c.eR gR).all (fun e => e * e == 1) &&
    (c.eR gR).all (fun e => (c.eR gR).all (fun f => e * f == f * e))

@[expose] def ECert.nCheck : Bool :=
  let El := (c.Es gR).toList
  let Ns := c.Ns gR
  closedH (c.nR gR) Ns && Ns.size == c.nOrd &&
    (c.nR gR).all (fun g => (c.eR gR).all fun e => El.any fun e' => g * e == e' * g)

end Check

section Sound

variable {G : Type} [Group G] [Finite G] {n : ℕ} {enc : G → RN n}

structure ECert.Sound (enc : G → RN n) (a b : G) (c : ECert) (E N : Subgroup G) : Prop where
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  sq : ∀ x ∈ E, x * x = 1
  cardE : Nat.card E = 16
  memE : ∀ x : G, x ∈ E ↔ enc x ∈ c.Es ([a, b, a⁻¹, b⁻¹].map enc)
  hN : N = Subgroup.normalizer (E : Set G)
  cardN : Nat.card N = c.nOrd
  memN : ∀ x : G, x ∈ N ↔ enc x ∈ c.Ns ([a, b, a⁻¹, b⁻¹].map enc)
  surjE : ∀ ε ∈ c.Es ([a, b, a⁻¹, b⁻¹].map enc), ∃ x ∈ E, enc x = ε
  surjN : ∀ ε ∈ c.Ns ([a, b, a⁻¹, b⁻¹].map enc), ∃ x ∈ N, enc x = ε

omit [Finite G] in
theorem enc_mem_of_mem_Es (h : IsEnc enc) (eG : List G) {r : RN n}
    (hr : r ∈ bfsSet (eG.map enc) 16) : ∃ x ∈ Subgroup.closure {g | g ∈ eG}, enc x = r :=
  bfsSet_sound h eG 16 r hr

theorem ECert.exists_soundCore (h : IsEnc enc) (a b : G) (c : ECert) (m : ℕ)
    (hm : m * c.nOrd = Nat.card G)
    (hc : (c.eCheck ([a, b, a⁻¹, b⁻¹].map enc) && c.nCheck ([a, b, a⁻¹, b⁻¹].map enc)) = true)
    (hbound : ∀ E : Subgroup G,
      (∀ x : G, x ∈ E ↔ enc x ∈ c.Es ([a, b, a⁻¹, b⁻¹].map enc)) →
      (∀ ε ∈ c.Es ([a, b, a⁻¹, b⁻¹].map enc), ∃ x ∈ E, enc x = ε) →
        m * Nat.card (Subgroup.normalizer (E : Set G)) ≤ Nat.card G) :
    ∃ E N : Subgroup G, c.Sound enc a b E N := by
  classical
  set gl : List G := [a, b, a⁻¹, b⁻¹] with hgl
  set gR : List (RN n) := gl.map enc with hgR
  set eG : List G := c.eW.map (evalW gl) with heG
  set nG : List G := c.nW.map (evalW gl) with hnG
  have heR : c.eR gR = eG.map enc := by
    simp only [ECert.eR, heG, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp [Function.comp, enc_evalW h, hgR]
  have hnR : c.nR gR = nG.map enc := by
    simp only [ECert.nR, hnG, List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp [Function.comp, enc_evalW h, hgR]
  have hEs : c.Es gR = bfsSet (eG.map enc) 16 := by simp only [ECert.Es, heR]
  have hNs : c.Ns gR = bfsSet (nG.map enc) c.depth := by simp only [ECert.Ns, hnR]
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hE, hN⟩ := hc
  simp only [ECert.eCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hE
  obtain ⟨⟨⟨hEcl, hEsize⟩, hEsq⟩, hEcomm⟩ := hE
  have hcl1 : closedH (eG.map enc) (bfsSet (eG.map enc) 16) = true := by
    rw [← hEs, ← heR]; exact hEcl
  have hmemE := mem_closure_iff_H h eG 16 hcl1
  have hcardE := card_closure_of_closedH h eG 16 hcl1
  have hsizeE : (bfsSet (eG.map enc) 16).size = 16 := by rw [← hEs]; exact hEsize
  have hEsqG : ∀ g ∈ eG, g * g = 1 := by
    intro g hg
    have := hEsq (enc g) (by rw [heR]; exact List.mem_map_of_mem hg)
    apply h.inj
    rw [h.map_mul, h.map_one]
    exact this
  have hEcommG : ∀ g ∈ eG, ∀ g' ∈ eG, g * g' = g' * g := by
    intro g hg g' hg'
    have := hEcomm (enc g) (by rw [heR]; exact List.mem_map_of_mem hg) (enc g')
      (by rw [heR]; exact List.mem_map_of_mem hg')
    apply h.inj
    rw [h.map_mul, h.map_mul]
    exact this
  set E : Subgroup G := Subgroup.closure {g | g ∈ eG} with hEdef
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    closure_comm (S := {g | g ∈ eG}) hEcommG
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hEsqG x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ihx, inv_one]
  simp only [ECert.nCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.any_eq_true] at hN
  obtain ⟨⟨hNcl, hNsize⟩, hNnorm⟩ := hN
  have hclN : closedH (nG.map enc) (bfsSet (nG.map enc) c.depth) = true := by
    rw [← hNs, ← hnR]; exact hNcl
  have hmemN := mem_closure_iff_H h nG c.depth hclN
  have hcardN := card_closure_of_closedH h nG c.depth hclN
  have hsizeN : (bfsSet (nG.map enc) c.depth).size = c.nOrd := by rw [← hNs]; exact hNsize
  set N₀ : Subgroup G := Subgroup.closure {g | g ∈ nG} with hN₀def
  have hnormgen : ∀ g ∈ nG, g ∈ Subgroup.normalizer (E : Set G) := by
    intro g hg
    have hconj : ∀ e ∈ eG, g * e * g⁻¹ ∈ E := by
      intro e he
      obtain ⟨e', he', hee'⟩ := hNnorm (enc g) (by rw [hnR]; exact List.mem_map_of_mem hg) (enc e)
        (by rw [heR]; exact List.mem_map_of_mem he)
      rw [hEs] at he'
      obtain ⟨x, hxE, hx⟩ := bfsSet_sound h eG 16 e' (Std.HashSet.mem_toList.1 he')
      have h1 : g * e = x * g := by
        apply h.inj
        rw [h.map_mul, h.map_mul, hx]
        exact hee'
      have h2 : g * e * g⁻¹ = x := by rw [h1]; group
      rw [h2]
      exact hxE
    apply mem_normalizer_of_conj_le
    have hle : E ≤ E.comap (MulAut.conj g).toMonoidHom := by
      rw [hEdef, Subgroup.closure_le]
      intro e he
      exact hconj e he
    intro x hx
    exact hle hx
  have hN₀le : N₀ ≤ Subgroup.normalizer (E : Set G) := by
    rw [hN₀def, Subgroup.closure_le]
    exact fun g hg => hnormgen g hg
  have hmemEs : ∀ ε : RN n, ε ∈ c.Es gR → ∃ x ∈ E, enc x = ε := by
    intro ε hε
    rw [hEs] at hε
    exact bfsSet_sound h eG 16 ε hε
  have hmN : m * Nat.card (Subgroup.normalizer (E : Set G)) ≤ Nat.card G :=
    hbound E (fun x => by rw [hmemE x, hEs]) hmemEs
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hm
      omega
    · exact h0
  have hNle : Nat.card (Subgroup.normalizer (E : Set G)) ≤ c.nOrd := by
    rw [← hm] at hmN
    exact Nat.le_of_mul_le_mul_left hmN hmpos
  have hN₀card : Nat.card N₀ = c.nOrd := by rw [hcardN, hsizeN]
  have hNeq : N₀ = Subgroup.normalizer (E : Set G) :=
    Subgroup.eq_of_le_of_card_ge hN₀le (by rw [hN₀card]; exact hNle)
  refine ⟨E, N₀, ?_⟩
  exact
    { comm := hcomm
      sq := hsq
      cardE := by rw [hcardE, hsizeE]
      memE := fun x => by rw [hmemE x, hEs]
      hN := hNeq
      cardN := hN₀card
      memN := fun x => by rw [hmemN x, hNs]
      surjE := fun ε hε => hmemEs ε hε
      surjN := fun ε hε => by
        rw [hNs] at hε
        exact bfsSet_sound h nG c.depth ε hε }

section Props

variable {n : ℕ}

@[expose] def isTransvecB (El : List (RN n)) (x : RN n) : Bool :=
  El.any fun u => x * u != u * x && El.all fun y => x * y == y * x || x * (u * y) == (u * y) * x

@[expose] def ECert.selfCentCheck (gR : List (RN n)) (c : ECert) : Bool :=
  let Es := c.Es gR
  let El := Es.toList
  (c.Ns gR).toList.all fun x => !(El.all fun e => x * e == e * x) || Es.contains x

@[expose] def ECert.hypACheck (gR : List (RN n)) (c : ECert) : Bool :=
  let El := (c.Es gR).toList
  c.selfCentCheck gR && (c.Ns gR).toList.all (fun x => !isTransvecB El x) &&
    (c.nOrd % 1920 == 0)

variable {G : Type} [Group G] [Finite G] {enc : G → RN n} {a b : G} {c : ECert} {E N : Subgroup G}

omit [Finite G] in
theorem ECert.Sound.centralizer_le (h : IsEnc enc) (hs : c.Sound enc a b E N)
    (hsc : c.selfCentCheck ([a, b, a⁻¹, b⁻¹].map enc) = true) :
    Subgroup.centralizer (E : Set G) ≤ E := by
  intro g hg
  have hgc : ∀ e ∈ E, g * e = e * g := fun e he =>
    (Subgroup.mem_centralizer_iff.1 hg e he).symm
  have hgN : g ∈ N := by
    rw [hs.hN, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : g * x * g⁻¹ = x := by rw [hgc x hx]; group
      rw [this]; exact hx
    · intro hy
      have h1 : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * g) := by rw [mul_assoc]
          _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [← hgc _ hy]
          _ = g * x * g⁻¹ := by group
      rw [h1]; exact hy
  have hgNs : enc g ∈ c.Ns ([a, b, a⁻¹, b⁻¹].map enc) := (hs.memN g).1 hgN
  simp only [ECert.selfCentCheck, List.all_eq_true] at hsc
  have h2 := hsc (enc g) (Std.HashSet.mem_toList.2 hgNs)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Std.HashSet.contains_iff_mem] at h2
  rcases h2 with h2 | h2
  · exfalso
    have : (c.Es ([a, b, a⁻¹, b⁻¹].map enc)).toList.all
        (fun e => enc g * e == e * enc g) = true := by
      rw [List.all_eq_true]
      intro e he
      obtain ⟨y, hy, rfl⟩ := hs.surjE e (Std.HashSet.mem_toList.1 he)
      simp only [beq_iff_eq]
      rw [← h.map_mul, ← h.map_mul, hgc y hy]
    rw [this] at h2
    exact absurd h2 (by simp)
  · exact (hs.memE g).2 h2

omit [Finite G] in
theorem ECert.Sound.hypA (h : IsEnc enc) (hs : c.Sound enc a b E N)
    (hck : c.hypACheck ([a, b, a⁻¹, b⁻¹].map enc) = true) : LocHypA E := by
  simp only [ECert.hypACheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq]
    at hck
  obtain ⟨⟨hsc, hnt⟩, h1920⟩ := hck
  refine ⟨hs.centralizer_le h hsc, ?_, ?_⟩
  · rw [← hs.hN, hs.cardN]
    exact Nat.dvd_of_mod_eq_zero h1920
  · intro m hm hT
    have hmN : m ∈ N := by rw [hs.hN]; exact hm
    have hmNs := (hs.memN m).1 hmN
    have h2 := hnt (enc m) (Std.HashSet.mem_toList.2 hmNs)
    obtain ⟨u, hu, hne, hx⟩ := hT
    rw [isTransvecB] at h2
    simp only [List.any_eq_false] at h2
    apply h2 (enc u) (Std.HashSet.mem_toList.2 ((hs.memE u).1 hu))
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨?_, ?_⟩
    · intro heq
      apply hne
      apply h.inj
      rw [h.map_mul, h.map_mul]
      exact heq
    · intro y hy
      obtain ⟨y', hy', rfl⟩ := hs.surjE y (Std.HashSet.mem_toList.1 hy)
      rcases hx y' hy' with h3 | h3
      · left
        rw [← h.map_mul, ← h.map_mul, h3]
      · right
        rw [← h.map_mul, ← h.map_mul, ← h.map_mul, h3]

end Props

end Sound

end CFSG.QuasithinUnique.A5.Kc3Cert
