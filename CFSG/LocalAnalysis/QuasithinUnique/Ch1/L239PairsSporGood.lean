module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporCert
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Good

variable {X : Type*} [Group X] [Finite X] [DecidableEq X] {E : Type*} [DecidableEq E]

omit [Group X] [Finite X] [DecidableEq X] [DecidableEq E] in
theorem mem_map_enc {enc : X → E} (henc : Function.Injective enc) {L : List X} {x : X} :
    enc x ∈ L.map enc ↔ x ∈ L := List.mem_map_of_injective henc

theorem not_dvd_chi0_168 : ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ 168) := by
  intro n hn hd
  rcases Nat.lt_or_ge n 3 with h | h
  · have : n = 2 := by omega
    subst this
    norm_num at hd
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h64 : 64 ≤ 4 ^ n := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h504 : 504 ≤ 2 ^ n * (4 ^ n - 1) := by
      calc 504 = 8 * 63 := by norm_num
        _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h8 (by omega)
    have := Nat.le_of_dvd (by norm_num) hd
    omega

theorem mem_normalizer_of_gens (enc : X → E) (henc : Function.Injective enc) (A : Subgroup X)
    (Al gens : List X) (hA : ∀ y, y ∈ A ↔ y ∈ Al) (hgens : ∀ a ∈ gens, a ∈ Al)
    (hcl : ∀ y ∈ Al, y ∈ Subgroup.closure {x | x ∈ gens}) (g : X) :
    g ∈ Subgroup.normalizer (A : Set X) ↔ nrmTestGens enc (Al.map enc) gens g = true := by
  have hAeq : A = Subgroup.closure {x | x ∈ gens} := by
    apply le_antisymm
    · intro y hy
      exact hcl y ((hA y).1 hy)
    · rw [Subgroup.closure_le]
      intro a ha
      exact (hA a).2 (hgens a ha)
  simp only [nrmTestGens, List.all_eq_true, decide_eq_true_eq, mem_map_enc henc]
  constructor
  · intro hg a ha
    have haA : a ∈ A := (hA a).2 (hgens a ha)
    exact (hA _).1 ((Subgroup.mem_normalizer_iff.1 hg a).1 haA)
  · intro h
    have hcl' : ∀ y ∈ Subgroup.closure {x | x ∈ gens}, g * y * g⁻¹ ∈ A := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem a ha => exact (hA _).2 (h a ha)
      | one => simp
      | mul a b _ _ ha hb =>
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]
        exact A.mul_mem ha hb
      | inv a _ ha =>
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]
        exact A.inv_mem ha
    have hfwd : ∀ y ∈ A, g * y * g⁻¹ ∈ A := fun y hy => hcl' y (hAeq ▸ hy)
    have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
      rintro _ ⟨y, hy, rfl⟩
      exact hfwd y hy
    have hcard : Nat.card A ≤ Nat.card (A.map (MulAut.conj g).toMonoidHom) :=
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => hfwd y hy, fun hy => ?_⟩
    have : g * y * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hy
    obtain ⟨y', hy', hyy⟩ := this
    have : y' = y := (MulAut.conj g).injective (by simpa using hyy)
    rw [← this]
    exact hy'

omit [Finite X] [DecidableEq X] in
theorem comm_mem_of_gens (S Z : Subgroup X) (gens : List X)
    (hS : S = Subgroup.closure {g | g ∈ gens}) (hZ : ∀ z ∈ Z, ∀ s ∈ S, s * z = z * s) (y : X)
    (h : ∀ s ∈ gens, y * s * y⁻¹ * s⁻¹ ∈ Z) : ∀ s ∈ S, y * s * y⁻¹ * s⁻¹ ∈ Z := by
  intro s hs
  rw [hS] at hs
  induction hs using Subgroup.closure_induction with
  | mem a ha => exact h a ha
  | one => simp
  | mul a b ha' hb' ha hb =>
    have haS : a ∈ S := hS ▸ ha'
    have hc : a * (y * b * y⁻¹ * b⁻¹) = (y * b * y⁻¹ * b⁻¹) * a := hZ _ hb a haS
    have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
        (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e, hc]
    have : (y * b * y⁻¹ * b⁻¹) * a * a⁻¹ = y * b * y⁻¹ * b⁻¹ := by group
    rw [this]
    exact Z.mul_mem ha hb
  | inv a ha' ha =>
    have haS : a ∈ S := hS ▸ ha'
    have hc : a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a = (y * a * y⁻¹ * a⁻¹)⁻¹ := by
      have := hZ _ (Z.inv_mem ha) a haS
      calc a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a = a⁻¹ * ((y * a * y⁻¹ * a⁻¹)⁻¹ * a) := by group
        _ = a⁻¹ * (a * (y * a * y⁻¹ * a⁻¹)⁻¹) := by rw [this]
        _ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
    have e : y * a⁻¹ * y⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
    rw [e, hc]
    exact Z.inv_mem ha

theorem goodLocal_of_gens (enc : X → E) (henc : Function.Injective enc) (Kx : Subgroup X)
    (Kl : List X) (hK : ∀ x, x ∈ Kx ↔ x ∈ Kl) (hKnd : Kl.Nodup) (kgens : List X)
    (hKcl : ∀ x ∈ Kl, x ∈ Subgroup.closure {g | g ∈ kgens}) (Ql : List X) (hQnd : Ql.Nodup)
    (hQK : ∀ q ∈ Ql, q ∈ Kl) (h1 : (1 : X) ∈ Ql)
    (hmul : ∀ p ∈ Ql, ∀ q ∈ Ql, enc (p * q) ∈ Ql.map enc)
    (hnorm : ∀ k ∈ kgens, ∀ q ∈ Ql,
      enc (k * q * k⁻¹) ∈ Ql.map enc ∧ enc (k⁻¹ * q * k) ∈ Ql.map enc)
    {a : ℕ} (h2 : ∀ q ∈ Ql, q ^ (2 ^ a) = 1)
    (hcent : ∀ y ∈ Kl, (∀ q ∈ Ql, enc (y * q) = enc (q * y)) → enc y ∈ Ql.map enc)
    (hA3 : ∀ b ∈ Kl, b ≠ 1 → b ^ 3 = 1 →
      4 < ((Ql.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length)
    (hN : ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ Kl.length / Ql.length)) :
    GoodLocal Kx := by
  classical
  have hmul' : ∀ p ∈ Ql, ∀ q ∈ Ql, p * q ∈ Ql := fun p hp q hq =>
    (mem_map_enc henc).1 (hmul p hp q hq)
  obtain ⟨Qx, hQx⟩ := subgroupOfList_exists Ql h1 hmul'
  have hgen : ∀ k ∈ kgens, ∀ q ∈ Qx, k * q * k⁻¹ ∈ Qx ∧ k⁻¹ * q * k ∈ Qx := by
    intro k hk q hq
    have h := hnorm k hk q ((hQx q).1 hq)
    exact ⟨(hQx _).2 ((mem_map_enc henc).1 h.1), (hQx _).2 ((mem_map_enc henc).1 h.2)⟩
  have hall : ∀ k ∈ Subgroup.closure {g | g ∈ kgens},
      ∀ q ∈ Qx, k * q * k⁻¹ ∈ Qx ∧ k⁻¹ * q * k ∈ Qx := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem g hg => exact hgen g hg
    | one => intro q hq; simpa using hq
    | mul a b _ _ ha hb =>
      intro q hq
      refine ⟨?_, ?_⟩
      · have := (ha _ (hb q hq).1).1
        simpa [mul_assoc] using this
      · have := (hb _ (ha q hq).2).2
        simpa [mul_assoc] using this
    | inv a _ ha =>
      intro q hq
      exact ⟨by simpa using (ha q hq).2, by simpa using (ha q hq).1⟩
  have hnorm' : ∀ k ∈ Kl, ∀ q ∈ Ql, k * q * k⁻¹ ∈ Ql := fun k hk q hq =>
    (hQx _).1 ((hall k (hKcl k hk) q ((hQx q).2 hq)).1)
  have hcent' : ∀ y ∈ Kl, (∀ q ∈ Ql, y * q = q * y) → y ∈ Ql := by
    intro y hy h
    exact (mem_map_enc henc).1 (hcent y hy fun q hq => by rw [h q hq])
  have hA3' : ∀ b ∈ Kl, b ≠ 1 → b ^ 3 = 1 →
      4 < (Ql.map fun q => q * b * q⁻¹ * b⁻¹).dedup.length := by
    intro b hb hb1 hb3
    have h := hA3 b hb hb1 hb3
    have e : (Ql.map fun q => enc (q * b * q⁻¹ * b⁻¹)) =
        (Ql.map fun q => q * b * q⁻¹ * b⁻¹).map enc := by
      simp [List.map_map, Function.comp_def]
    rw [e, List.dedup_map_of_injective henc, List.length_map] at h
    exact h
  exact goodLocal_of_lists Kx Kl hK hKnd Ql hQnd hQK h1 hmul' hnorm' h2 hcent' hA3' hN

end Good

section Canonical

variable {X : Type*} [Group X]

@[expose] def z2Set (S : Subgroup X) : Set X :=
  {y | y ∈ S ∧ ∀ s ∈ S, y * s * y⁻¹ * s⁻¹ ∈ canonZ S}

@[expose] def canonC2 (S : Subgroup X) : Subgroup X := S ⊓ Subgroup.centralizer (z2Set S)

theorem mem_canonC2 {S : Subgroup X} {x : X} :
    x ∈ canonC2 S ↔ x ∈ S ∧ ∀ y ∈ S, (∀ s ∈ S, y * s * y⁻¹ * s⁻¹ ∈ canonZ S) → y * x = x * y := by
  simp only [canonC2, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, z2Set]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h y hy hyz
    exact h y ⟨hy, hyz⟩
  · rintro h y ⟨hy, hyz⟩
    exact h y hy hyz

theorem canonC2_map (α : X ≃* X) (S : Subgroup X) :
    (canonC2 S).map α.toMonoidHom = canonC2 (S.map α.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy : y ∈ canonC2 S := hy
    rw [mem_canonC2] at hy
    rw [mem_canonC2]
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩ hwz
    have hwz' : ∀ s ∈ S, w * s * w⁻¹ * s⁻¹ ∈ canonZ S := by
      intro s hs
      have h := hwz (α s) ⟨s, hs, rfl⟩
      rw [← canonZ_map] at h
      obtain ⟨v, hv, hv'⟩ := h
      have : v = w * s * w⁻¹ * s⁻¹ := α.injective (by simpa using hv')
      rw [← this]
      exact hv
    have := hy.2 w hw hwz'
    have := congrArg α this
    simpa using this
  · intro hx
    rw [mem_canonC2] at hx
    obtain ⟨⟨y, hy, rfl⟩, h⟩ := hx
    refine ⟨y, ?_, rfl⟩
    show y ∈ canonC2 S
    rw [mem_canonC2]
    refine ⟨hy, fun w hw hwz => ?_⟩
    have hwz' : ∀ s ∈ S.map α.toMonoidHom,
        α w * s * (α w)⁻¹ * s⁻¹ ∈ canonZ (S.map α.toMonoidHom) := by
      rintro _ ⟨s, hs, rfl⟩
      rw [← canonZ_map]
      exact ⟨w * s * w⁻¹ * s⁻¹, hwz s hs, by simp⟩
    have := h (α w) ⟨w, hw, rfl⟩ hwz'
    apply α.injective
    simpa using this

end Canonical

end CFSG.QuasithinUnique.Vol2Native.L239
