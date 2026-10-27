module

public import CFSG.Permutation.UnitaryThreeRecognition.Fixed
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.AGLEmbedding.CenterOver

open CFSG.UnitaryThreeRecognition MulAction
open scoped Pointwise

section Defs

variable {G Ω : Type*} [Group G] [MulAction G Ω]

structure UnitalData (p f : ℕ) (Q Z : Subgroup G) (a b : Ω) (ι : G) : Prop where
  two : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w
  root : IsRootSubgroup Q a
  ne : b ≠ a
  mem : ι ∈ pairStab G a b
  sq : ι * ι = 1
  ne_one : ι ≠ 1
  uniq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = ι
  cent : centQ Q ι = Z
  normQ : ∀ r ∈ Q, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z
  normZ : ∀ g : G, g • a = a → ∀ z ∈ Z, g * z * g⁻¹ ∈ Z
  card : Nat.card Q = Nat.card Z ^ 3
  pf : Nat.card Z = p ^ f
  coprime : ¬ p ∣ Nat.card (pairStab G a b)

def Closed (S : Set Ω) : Prop :=
  ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → ∀ j : G, j * j = 1 → j ≠ 1 → j • x = x → j • x' = x' →
    ∀ t : Ω, j • t = t → t ∈ S

theorem Closed.smul {S : Set Ω} (hS : Closed (G := G) S) (g : G) :
    Closed (G := G) (g • S) := by
  intro x hx x' hx' hne j hj hjn hjx hjx' t ht
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx hx' ⊢
  have hfix : ∀ y : Ω, j • y = y → (g⁻¹ * j * g) • (g⁻¹ • y) = g⁻¹ • y := by
    intro y hy
    rw [mul_smul, mul_smul, smul_inv_smul, hy]
  refine hS _ hx _ hx' (fun h => hne ?_) (g⁻¹ * j * g) ?_ ?_ (hfix x hjx) (hfix x' hjx') _
    (hfix t ht)
  · exact (MulAction.injective g⁻¹) h
  · calc g⁻¹ * j * g * (g⁻¹ * j * g) = g⁻¹ * (j * j) * g := by group
      _ = 1 := by rw [hj]; group
  · intro h
    apply hjn
    have : j = g * (g⁻¹ * j * g) * g⁻¹ := by group
    rw [this, h]
    group

end Defs

namespace UnitalData

variable {G Ω : Type*} [Group G] [MulAction G Ω] {p f : ℕ} {Q Z : Subgroup G} {a b : Ω} {ι : G}
  (D : UnitalData p f Q Z a b ι)

include D

theorem Z_le_Q : Z ≤ Q := D.cent ▸ inf_le_left

theorem exists_smul_eq (x y : Ω) : ∃ g : G, g • x = y := by
  obtain ⟨x', hx'⟩ : ∃ x' : Ω, x' ≠ x := by
    by_cases h : x = a
    · exact ⟨b, fun h' => D.ne (h'.trans h)⟩
    · exact ⟨a, fun h' => h h'.symm⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Ω, y' ≠ y := by
    by_cases h : y = a
    · exact ⟨b, fun h' => D.ne (h'.trans h)⟩
    · exact ⟨a, fun h' => h h'.symm⟩
  obtain ⟨g, hg, -⟩ := D.two hx'.symm hy'.symm
  exact ⟨g, hg⟩

theorem exists_conj_pair {x y : Ω} (hxy : x ≠ y) : ∃ g : G, g • a = x ∧ g • b = y :=
  D.two D.ne.symm hxy

theorem inv_unique {x y : Ω} (hxy : x ≠ y) {t₁ t₂ : G} (h₁ : t₁ ∈ pairStab G x y)
    (h₂ : t₂ ∈ pairStab G x y) (hs₁ : t₁ * t₁ = 1) (hs₂ : t₂ * t₂ = 1) (hn₁ : t₁ ≠ 1)
    (hn₂ : t₂ ≠ 1) : t₁ = t₂ := by
  obtain ⟨g, hga, hgb⟩ := D.exists_conj_pair hxy
  have key : ∀ t ∈ pairStab G x y, t * t = 1 → t ≠ 1 → g⁻¹ * t * g = ι := by
    intro t ht hs hn
    have hmem : g⁻¹ * t * g ∈ pairStab G a b := by
      refine ⟨?_, ?_⟩
      · change (g⁻¹ * t * g) • a = a
        rw [mul_smul, mul_smul, hga, ht.1, inv_smul_eq_iff, hga]
      · change (g⁻¹ * t * g) • b = b
        rw [mul_smul, mul_smul, hgb, ht.2, inv_smul_eq_iff, hgb]
    have hs' : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [hs]; group
    rcases D.uniq _ hmem hs' with h | h
    · exfalso
      apply hn
      have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      rw [this, h]
      group
    · exact h
  have h12 := (key t₁ h₁ hs₁ hn₁).trans (key t₂ h₂ hs₂ hn₂).symm
  have := congrArg (fun s => g * s * g⁻¹) h12
  simpa [mul_assoc] using this

theorem exists_invol {b' : Ω} (hb' : b' ≠ a) :
    ∃ j ∈ pairStab G a b', j * j = 1 ∧ j ≠ 1 ∧ centQ Q j = Z := by
  obtain ⟨r, hrQ, hr⟩ := D.root.exists_smul_eq D.ne hb'
  have hra : r • a = a := D.root.smul_self hrQ
  have hrinva : r⁻¹ • a = a := by rw [inv_smul_eq_iff, hra]
  have hrinvb : r⁻¹ • b' = b := by rw [inv_smul_eq_iff, hr]
  refine ⟨r * ι * r⁻¹, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · change (r * ι * r⁻¹) • a = a
    rw [mul_smul, mul_smul, hrinva, D.mem.1, hra]
  · change (r * ι * r⁻¹) • b' = b'
    rw [mul_smul, mul_smul, hrinvb, D.mem.2, hr]
  · calc r * ι * r⁻¹ * (r * ι * r⁻¹) = r * (ι * ι) * r⁻¹ := by group
      _ = 1 := by rw [D.sq]; group
  · intro h
    apply D.ne_one
    have : ι = r⁻¹ * (r * ι * r⁻¹) * r := by group
    rw [this, h]
    group
  · ext u
    simp only [mem_centQ]
    constructor
    · rintro ⟨huQ, huj⟩
      have hu' : r⁻¹ * u * r ∈ centQ Q ι := by
        refine mem_centQ.mpr ⟨?_, ?_⟩
        · exact Q.mul_mem (Q.mul_mem (Q.inv_mem hrQ) huQ) hrQ
        · calc ι * (r⁻¹ * u * r) = r⁻¹ * ((r * ι * r⁻¹) * u) * r := by group
            _ = r⁻¹ * (u * (r * ι * r⁻¹)) * r := by rw [huj]
            _ = r⁻¹ * u * r * ι := by group
      rw [D.cent] at hu'
      have := D.normQ r hrQ _ hu'
      simpa [mul_assoc] using this
    · intro huZ
      have huQ : u ∈ Q := D.Z_le_Q huZ
      refine ⟨huQ, ?_⟩
      have hu' : r⁻¹ * u * r ∈ Z := by
        have := D.normQ r⁻¹ (Q.inv_mem hrQ) u huZ
        simpa using this
      have hc : ι * (r⁻¹ * u * r) = (r⁻¹ * u * r) * ι := by
        rw [← D.cent] at hu'
        exact (mem_centQ.mp hu').2
      calc r * ι * r⁻¹ * u = r * (ι * (r⁻¹ * u * r)) * r⁻¹ := by group
        _ = r * ((r⁻¹ * u * r) * ι) * r⁻¹ := by rw [hc]
        _ = u * (r * ι * r⁻¹) := by group

theorem centQ_eq {b' : Ω} (hb' : b' ≠ a) {j : G} (hj : j ∈ pairStab G a b') (hs : j * j = 1)
    (hn : j ≠ 1) : centQ Q j = Z := by
  obtain ⟨j', hj', hs', hn', hc'⟩ := D.exists_invol hb'
  have : j = j' := D.inv_unique hb'.symm hj hj' hs hs' hn hn'
  rw [this]
  exact hc'

theorem fix_iff {b' : Ω} (hb' : b' ≠ a) {j : G} (hj : j ∈ pairStab G a b') (hs : j * j = 1)
    (hn : j ≠ 1) (t : Ω) : j • t = t ↔ t = a ∨ ∃ u ∈ Z, t = u • b' := by
  have hc := D.centQ_eq hb' hj hs hn
  constructor
  · intro ht
    by_cases hta : t = a
    · exact Or.inl hta
    · obtain ⟨u, huQ, hu⟩ := D.root.exists_smul_eq hb' hta
      have hcomm : j * u = u * j := (D.root.fixes_iff hb' hj huQ).mp (by rw [hu]; exact ht)
      have hmem : u ∈ centQ Q j := mem_centQ.mpr ⟨huQ, hcomm⟩
      rw [hc] at hmem
      exact Or.inr ⟨u, hmem, hu.symm⟩
  · rintro (rfl | ⟨u, hu, rfl⟩)
    · exact hj.1
    · have huc : u ∈ centQ Q j := by rw [hc]; exact hu
      exact (D.root.fixes_iff hb' hj (mem_centQ.mp huc).1).mpr (mem_centQ.mp huc).2

theorem card_fix [Finite Ω] {b' : Ω} (hb' : b' ≠ a) {j : G} (hj : j ∈ pairStab G a b')
    (hs : j * j = 1) (hn : j ≠ 1) : Nat.card {t : Ω // j • t = t} = Nat.card Z + 1 := by
  rw [D.root.card_fixedPoints hb' hj, D.centQ_eq hb' hj hs hn]

theorem closed_orbit (Y : Subgroup G) (hZY : Z ≤ Y) :
    Closed (G := G) {x : Ω | ∃ y ∈ Y, y • a = x} := by
  rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ hne j hj hjn hjx hjx' t ht
  set b' : Ω := (y₁⁻¹ * y₂) • a with hb'
  have hb'a : b' ≠ a := by
    intro h
    apply hne
    rw [hb', mul_smul, inv_smul_eq_iff] at h
    rw [← h]
  have e : y₁ • b' = y₂ • a := by rw [hb', ← mul_smul, mul_inv_cancel_left]
  have hj1 : (y₁⁻¹ * j * y₁) ∈ pairStab G a b' := by
    refine ⟨?_, ?_⟩
    · change (y₁⁻¹ * j * y₁) • a = a
      calc (y₁⁻¹ * j * y₁) • a = y₁⁻¹ • (j • (y₁ • a)) := by simp only [mul_smul]
        _ = a := by rw [hjx, inv_smul_smul]
    · change (y₁⁻¹ * j * y₁) • b' = b'
      calc (y₁⁻¹ * j * y₁) • b' = y₁⁻¹ • (j • (y₁ • b')) := by simp only [mul_smul]
        _ = y₁⁻¹ • (j • (y₂ • a)) := by rw [e]
        _ = y₁⁻¹ • (y₂ • a) := by rw [hjx']
        _ = b' := by rw [hb', mul_smul]
  have hs : (y₁⁻¹ * j * y₁) * (y₁⁻¹ * j * y₁) = 1 := by
    calc (y₁⁻¹ * j * y₁) * (y₁⁻¹ * j * y₁) = y₁⁻¹ * (j * j) * y₁ := by group
      _ = 1 := by rw [hj]; group
  have hn : (y₁⁻¹ * j * y₁) ≠ 1 := by
    intro h
    apply hjn
    have : j = y₁ * (y₁⁻¹ * j * y₁) * y₁⁻¹ := by group
    rw [this, h]
    group
  have hfix : (y₁⁻¹ * j * y₁) • (y₁⁻¹ • t) = y₁⁻¹ • t := by
    calc (y₁⁻¹ * j * y₁) • (y₁⁻¹ • t) = y₁⁻¹ • (j • (y₁ • (y₁⁻¹ • t))) := by simp only [mul_smul]
      _ = y₁⁻¹ • t := by rw [smul_inv_smul, ht]
  have htt : t = y₁ • (y₁⁻¹ • t) := (smul_inv_smul y₁ t).symm
  rcases (D.fix_iff hb'a hj1 hs hn _).mp hfix with h | ⟨u, hu, h⟩
  · exact ⟨y₁, hy₁, by rw [htt, h]⟩
  · refine ⟨y₁ * u * (y₁⁻¹ * y₂), Y.mul_mem (Y.mul_mem hy₁ (hZY hu))
      (Y.mul_mem (Y.inv_mem hy₁) hy₂), ?_⟩
    rw [htt, h, hb']
    simp only [mul_smul]

theorem exists_invol_fixing {x : Ω} (hx : x ≠ a) {u : G} (hu : u ∈ Z) :
    ∃ j : G, j * j = 1 ∧ j ≠ 1 ∧ j • a = a ∧ j • x = x ∧ j • (u • x) = u • x := by
  obtain ⟨j, hj, hs, hn, hc⟩ := D.exists_invol hx
  have huj : j * u = u * j := by
    have : u ∈ centQ Q j := by rw [hc]; exact hu
    exact (mem_centQ.mp this).2
  refine ⟨j, hs, hn, hj.1, hj.2, ?_⟩
  rw [← mul_smul, huj, mul_smul, hj.2]

theorem mem_of_closed {S : Set Ω} (hS : Closed (G := G) S) {x : Ω} (hxS : x ∈ S) (hx : x ≠ a)
    {u : G} (hu : u ∈ Z) (hux : u • x ∈ S) (hne : u • x ≠ x) : a ∈ S := by
  obtain ⟨j, hs, hn, hja, hjx, hjux⟩ := D.exists_invol_fixing hx hu
  exact hS x hxS (u • x) hux hne.symm j hs hn hjx hjux a hja

theorem card_ne [Finite Ω] : Nat.card {x : Ω // x ≠ a} = Nat.card Q := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun u : Q => (⟨(u : G) • b, D.root.smul_ne u.2 D.ne⟩ : {x : Ω // x ≠ a})) ⟨?_, ?_⟩)
  · intro u v h
    exact Subtype.ext (D.root.eq_of_smul_eq u.2 v.2 D.ne (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    obtain ⟨u, huQ, hu⟩ := D.root.exists_smul_eq D.ne hx
    exact ⟨⟨u, huQ⟩, Subtype.ext hu⟩

theorem card_le_of_closed [Finite Ω] {S : Set Ω} (hS : Closed (G := G) S) (haS : a ∉ S) :
    Nat.card S * Nat.card Z ≤ Nat.card Z ^ 3 := by
  have hSa : ∀ x : S, (x : Ω) ≠ a := fun x h => haS (h ▸ x.2)
  let F : S × Z → {x : Ω // x ≠ a} := fun p =>
    ⟨(p.2 : G) • (p.1 : Ω), D.root.smul_ne (D.Z_le_Q p.2.2) (hSa p.1)⟩
  have hF : Function.Injective F := by
    rintro ⟨x, u⟩ ⟨x', u'⟩ h
    have h1 : (u : G) • (x : Ω) = (u' : G) • (x' : Ω) := congrArg Subtype.val h
    have hx' : (x' : Ω) = ((u' : G)⁻¹ * u) • (x : Ω) := by
      rw [mul_smul, h1, inv_smul_smul]
    by_cases hxx : (x : Ω) = x'
    · have huu : (u : G) = u' := by
        refine D.root.eq_of_smul_eq (D.Z_le_Q u.2) (D.Z_le_Q u'.2) (hSa x) ?_
        rw [h1, hxx]
      have hxx' : x = x' := Subtype.ext hxx
      subst hxx'
      rw [Subtype.ext huu]
    · exfalso
      have hv : (u' : G)⁻¹ * u ∈ Z := Z.mul_mem (Z.inv_mem u'.2) u.2
      apply haS
      refine D.mem_of_closed hS x.2 (hSa x) hv (hx' ▸ x'.2) ?_
      rw [← hx']
      exact fun h => hxx h.symm
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, D.card_ne, D.card] at this

theorem card_ge_of_fix [Finite Ω] {S : Set Ω} {j₁ : G} (hs : j₁ * j₁ = 1) (hn : j₁ ≠ 1)
    (haj : j₁ • a ≠ a) (hfix : ∀ t : Ω, j₁ • t = t → t ∈ S)
    (hZS : ∀ u ∈ Z, ∀ x ∈ S, u • x ∈ S)
    (hcard : Nat.card {t : Ω // j₁ • t = t} = Nat.card Z + 1) :
    (Nat.card Z + 1) * Nat.card Z ≤ Nat.card {x : Ω // x ∈ S ∧ x ≠ a} := by
  have hFa : ∀ x : {t : Ω // j₁ • t = t}, (x : Ω) ≠ a := fun x h => haj (h ▸ x.2)
  let F : {t : Ω // j₁ • t = t} × Z → {x : Ω // x ∈ S ∧ x ≠ a} := fun p =>
    ⟨(p.2 : G) • (p.1 : Ω), hZS _ p.2.2 _ (hfix _ p.1.2),
      D.root.smul_ne (D.Z_le_Q p.2.2) (hFa p.1)⟩
  have hF : Function.Injective F := by
    rintro ⟨x, u⟩ ⟨x', u'⟩ h
    have h1 : (u : G) • (x : Ω) = (u' : G) • (x' : Ω) := congrArg Subtype.val h
    have hx' : (x' : Ω) = ((u' : G)⁻¹ * u) • (x : Ω) := by
      rw [mul_smul, h1, inv_smul_smul]
    by_cases hxx : (x : Ω) = x'
    · have huu : (u : G) = u' := by
        refine D.root.eq_of_smul_eq (D.Z_le_Q u.2) (D.Z_le_Q u'.2) (hFa x) ?_
        rw [h1, hxx]
      have hxx' : x = x' := Subtype.ext hxx
      subst hxx'
      rw [Subtype.ext huu]
    · exfalso
      have hv : (u' : G)⁻¹ * u ∈ Z := Z.mul_mem (Z.inv_mem u'.2) u.2
      obtain ⟨j, hjs, hjn, hja, hjx, hjx'⟩ := D.exists_invol_fixing (hFa x) hv
      rw [← hx'] at hjx'
      have hj₁x : j₁ ∈ pairStab G (x : Ω) (x' : Ω) := ⟨x.2, x'.2⟩
      have hjxx : j ∈ pairStab G (x : Ω) (x' : Ω) := ⟨hjx, hjx'⟩
      have := D.inv_unique hxx hjxx hj₁x hjs hs hjn hn
      apply haj
      rw [← this]
      exact hja
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, hcard] at this

theorem eq_one_of_pow_eq_one [Fact p.Prime] {x y : Ω} (hxy : x ≠ y) {s : G}
    (hs : s ∈ pairStab G x y) {k : ℕ} (hk : s ^ p ^ k = 1) : s = 1 := by
  obtain ⟨g, hga, hgb⟩ := D.exists_conj_pair hxy
  have htmem : g⁻¹ * s * g ∈ pairStab G a b := by
    refine ⟨?_, ?_⟩
    · change (g⁻¹ * s * g) • a = a
      rw [mul_smul, mul_smul, hga, hs.1, inv_smul_eq_iff, hga]
    · change (g⁻¹ * s * g) • b = b
      rw [mul_smul, mul_smul, hgb, hs.2, inv_smul_eq_iff, hgb]
  have htk : (g⁻¹ * s * g) ^ p ^ k = 1 := by
    have h1 : (g⁻¹ * s * g) = (MulAut.conj g⁻¹ : MulAut G) s := by
      simp
    rw [h1, ← map_pow, hk, map_one]
  have hdvd1 : orderOf (g⁻¹ * s * g) ∣ p ^ k := orderOf_dvd_of_pow_eq_one htk
  have hdvd2 : orderOf (g⁻¹ * s * g) ∣ Nat.card (pairStab G a b) := by
    have := orderOf_dvd_natCard (⟨g⁻¹ * s * g, htmem⟩ : pairStab G a b)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd1
  have hm0 : m = 0 := by
    by_contra hne
    apply D.coprime
    refine Dvd.dvd.trans ?_ hdvd2
    rw [hm]
    exact dvd_pow_self p hne
  rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
  have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
  rw [this, hm]
  group

theorem card_le_of_pGroup [Finite G] [Finite Ω] [Fact p.Prime] (hf : 1 ≤ f) {O : Set Ω}
    (hO : Nat.card O = Nat.card Z + 1) {S : Subgroup G} (hS : IsPGroup p S)
    (hOS : ∀ s ∈ S, ∀ x ∈ O, s • x ∈ O) : Nat.card S ≤ Nat.card Z := by
  classical
  let sub : SubMulAction S Ω := { carrier := O, smul_mem' := fun s x hx => hOS s s.2 x hx }
  have hmod := hS.card_modEq_card_fixedPoints ↥sub
  have hcardsub : Nat.card ↥sub = Nat.card O := rfl
  have hp1 : Nat.card ↥sub ≡ 1 [MOD p] := by
    rw [hcardsub, hO, D.pf]
    have h0 : p ^ f ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by omega))
    simpa using h0.add_right 1
  have hfix : Nat.card ↥(fixedPoints S ↥sub) ≠ 0 := by
    intro h
    rw [h] at hmod
    have h1 : 1 ≡ 0 [MOD p] := hp1.symm.trans hmod
    have := Nat.modEq_zero_iff_dvd.mp h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨⟨x₀, hx₀O⟩, hx₀fix⟩ : ∃ x : ↥sub, x ∈ fixedPoints S ↥sub := by
    have hpos := Nat.pos_of_ne_zero hfix
    obtain ⟨⟨x, hx⟩, -⟩ := Nat.card_pos_iff.mp hpos
    exact ⟨x, hx⟩
  have hx₀ : ∀ s ∈ S, s • x₀ = x₀ := by
    intro s hs
    have := hx₀fix ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hZpos : 0 < Nat.card Z := by rw [D.pf]; exact pow_pos (Fact.out : p.Prime).pos f
  have hnt : Nontrivial O := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨⟨y, hyO⟩, hy⟩ := exists_ne (⟨x₀, hx₀O⟩ : O)
  have hyx : y ≠ x₀ := fun h => hy (Subtype.ext h)
  let F : Option S → O := fun o => match o with
    | none => ⟨x₀, hx₀O⟩
    | some s => ⟨(s : G) • y, hOS s s.2 y hyO⟩
  have hF : Function.Injective F := by
    have hsome : ∀ s : S, (s : G) • y ≠ x₀ := by
      intro s h
      apply hyx
      rw [smul_eq_iff_eq_inv_smul] at h
      rw [h]
      exact hx₀ _ (S.inv_mem s.2)
    intro o₁ o₂ h
    have hv := congrArg Subtype.val h
    rcases o₁ with _ | s₁ <;> rcases o₂ with _ | s₂
    · rfl
    · exact absurd hv.symm (hsome s₂)
    · exact absurd hv (hsome s₁)
    · congr 1
      have h1 : (s₁ : G) • y = (s₂ : G) • y := hv
      have hmem : (s₁ : G)⁻¹ * s₂ ∈ pairStab G x₀ y := by
        refine ⟨?_, ?_⟩
        · change ((s₁ : G)⁻¹ * s₂) • x₀ = x₀
          rw [mul_smul, hx₀ s₂ s₂.2, inv_smul_eq_iff, hx₀ s₁ s₁.2]
        · change ((s₁ : G)⁻¹ * s₂) • y = y
          rw [mul_smul, ← h1, inv_smul_smul]
      obtain ⟨k, hk⟩ := hS (s₁⁻¹ * s₂)
      have hk' : ((s₁ : G)⁻¹ * s₂) ^ p ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have := D.eq_one_of_pow_eq_one hyx.symm hmem hk'
      apply Subtype.ext
      have h2 : (s₂ : G) = s₁ := by
        have := congrArg ((s₁ : G) * ·) this
        simpa using this
      exact h2.symm
  have := Nat.card_le_card_of_injective F hF
  rw [Finite.card_option, hO] at this
  omega

omit D in
theorem card_fix_conj [Finite Ω] (j g : G) :
    Nat.card {t : Ω // (g * j * g⁻¹) • t = t} = Nat.card {t : Ω // j • t = t} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun t => ?_)
  change (g * j * g⁻¹) • t = t ↔ j • (g⁻¹ • t) = g⁻¹ • t
  rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul]

theorem dichotomy [Finite G] [Finite Ω] [Fact p.Prime] (hf : 1 ≤ f) (Y : Subgroup G)
    (hZY : Z ≤ Y) (hY : ¬ Y ≤ stabilizer G a) :
    (∀ g : G, ∀ z ∈ Z, g * z * g⁻¹ ∈ Y) ∨
      (∀ S : Subgroup G, S ≤ Y → IsPGroup p S → Nat.card S ≤ Nat.card Z) := by
  classical
  set O : Set Ω := {x | ∃ y ∈ Y, y • a = x} with hO
  have hcl : Closed (G := G) O := D.closed_orbit Y hZY
  have haO : a ∈ O := ⟨1, Y.one_mem, one_smul _ _⟩
  have hYinv : ∀ y ∈ Y, ∀ x ∈ O, y • x ∈ O := by
    rintro y hy _ ⟨y', hy', rfl⟩
    exact ⟨y * y', Y.mul_mem hy hy', mul_smul _ _ _⟩
  obtain ⟨y₀, hy₀, hy₀a⟩ : ∃ y ∈ Y, y • a ≠ a := by
    by_contra h
    push Not at h
    exact hY fun y hy => h y hy
  have hb'O : y₀ • a ∈ O := ⟨y₀, hy₀, rfl⟩
  obtain ⟨j₀, hj₀, hs₀, hn₀, -⟩ := D.exists_invol hy₀a
  have hfixO : ∀ t : Ω, j₀ • t = t → t ∈ O := fun t ht =>
    hcl a haO (y₀ • a) hb'O (Ne.symm hy₀a) j₀ hs₀ hn₀ hj₀.1 hj₀.2 t ht
  have hcard₀ : Nat.card {t : Ω // j₀ • t = t} = Nat.card Z + 1 :=
    D.card_fix hy₀a hj₀ hs₀ hn₀
  by_cases hcol : ∀ x ∈ O, j₀ • x = x
  · right
    have hOeq : O = {t | j₀ • t = t} := Set.ext fun t => ⟨hcol t, hfixO t⟩
    have hcard : Nat.card O = Nat.card Z + 1 := by rw [hOeq]; exact hcard₀
    exact fun S hSY hS => D.card_le_of_pGroup hf hcard hS fun s hs x hx => hYinv s (hSY hs) x hx
  · left
    push Not at hcol
    obtain ⟨c, hcO, hcj⟩ := hcol
    have hall : ∀ x : Ω, x ∈ O := by
      by_contra hne
      push Not at hne
      obtain ⟨z, hzO⟩ := hne
      obtain ⟨yc, hyc, hyca⟩ := hcO
      have hy₁c : yc⁻¹ • c = a := by rw [← hyca, inv_smul_smul]
      set j₁ : G := yc⁻¹ * j₀ * (yc⁻¹)⁻¹ with hj₁
      have hj₁s : j₁ * j₁ = 1 := by
        calc j₁ * j₁ = yc⁻¹ * (j₀ * j₀) * (yc⁻¹)⁻¹ := by rw [hj₁]; group
          _ = 1 := by rw [hs₀]; group
      have hj₁n : j₁ ≠ 1 := by
        intro h
        apply hn₀
        have : j₀ = (yc⁻¹)⁻¹ * j₁ * yc⁻¹ := by rw [hj₁]; group
        rw [this, h]
        group
      have hj₁a : j₁ • a ≠ a := by
        intro h
        apply hcj
        have h1 : j₁ • a = a := h
        rw [hj₁] at h1
        have h2 : (yc⁻¹ * j₀ * (yc⁻¹)⁻¹) • (yc⁻¹ • c) = yc⁻¹ • c := by rw [hy₁c]; exact h1
        have h3 : yc⁻¹ • (j₀ • c) = yc⁻¹ • c := by
          calc yc⁻¹ • (j₀ • c) = (yc⁻¹ * j₀ * (yc⁻¹)⁻¹) • (yc⁻¹ • c) := by simp [mul_smul]
            _ = yc⁻¹ • c := h2
        exact (MulAction.injective yc⁻¹) h3
      have hfix₁ : ∀ t : Ω, j₁ • t = t → t ∈ O := by
        intro t ht
        have h1 : j₀ • (yc • t) = yc • t := by
          have : (yc⁻¹ * j₀ * (yc⁻¹)⁻¹) • t = t := ht
          calc j₀ • (yc • t) = yc • ((yc⁻¹ * j₀ * (yc⁻¹)⁻¹) • t) := by simp [mul_smul]
            _ = yc • t := by rw [this]
        have h2 := hfixO _ h1
        have := hYinv yc⁻¹ (Y.inv_mem hyc) _ h2
        rwa [inv_smul_smul] at this
      have hcard₁ : Nat.card {t : Ω // j₁ • t = t} = Nat.card Z + 1 := by
        rw [hj₁, card_fix_conj, hcard₀]
      have hlow := D.card_ge_of_fix hj₁s hj₁n hj₁a hfix₁
        (fun u hu x hx => hYinv u (hZY hu) x hx) hcard₁
      have hOcard : Nat.card {x : Ω // x ∈ O ∧ x ≠ a} + 1 ≤ Nat.card O := by
        let F : Option {x : Ω // x ∈ O ∧ x ≠ a} → O := fun o => match o with
          | none => ⟨a, haO⟩
          | some x => ⟨x.1, x.2.1⟩
        have hF : Function.Injective F := by
          intro o₁ o₂ h
          have hv := congrArg Subtype.val h
          rcases o₁ with _ | x₁ <;> rcases o₂ with _ | x₂
          · rfl
          · exact absurd hv.symm x₂.2.2
          · exact absurd hv x₁.2.2
          · exact congrArg some (Subtype.ext hv)
        have := Nat.card_le_card_of_injective F hF
        rwa [Finite.card_option] at this
      obtain ⟨g, hg⟩ := D.exists_smul_eq z a
      have haS : a ∉ g • O := by
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        have : g⁻¹ • a = z := by rw [← hg, inv_smul_smul]
        rw [this]
        exact hzO
      have hup := D.card_le_of_closed (hcl.smul g) haS
      have hSO : Nat.card ((g • O : Set Ω)) = Nat.card O :=
        (Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g) fun x => by
          change x ∈ O ↔ g • x ∈ g • O
          exact (Set.smul_mem_smul_set_iff).symm)).symm
      rw [hSO] at hup
      have hZpos : 0 < Nat.card Z := by rw [D.pf]; exact pow_pos (Fact.out : p.Prime).pos f
      have e1 : (Nat.card Z + 1) * Nat.card Z = Nat.card Z ^ 2 + Nat.card Z := by ring
      rw [e1] at hlow
      have h1 : (Nat.card Z ^ 2 + Nat.card Z + 1) * Nat.card Z ≤ Nat.card O * Nat.card Z :=
        Nat.mul_le_mul_right _ (by omega)
      have e2 : (Nat.card Z ^ 2 + Nat.card Z + 1) * Nat.card Z =
          Nat.card Z ^ 3 + Nat.card Z ^ 2 + Nat.card Z := by ring
      rw [e2] at h1
      omega
    intro g z hz
    obtain ⟨y, hy, hyg⟩ := hall (g • a)
    have hh : (y⁻¹ * g) • a = a := by rw [mul_smul, ← hyg, inv_smul_smul]
    have hzh := D.normZ (y⁻¹ * g) hh z hz
    have : g * z * g⁻¹ = y * ((y⁻¹ * g) * z * (y⁻¹ * g)⁻¹) * y⁻¹ := by group
    rw [this]
    exact Y.mul_mem (Y.mul_mem hy (hZY hzh)) (Y.inv_mem hy)

end UnitalData

theorem not_isSolvable_of_surjective {Y K : Type*} [Group Y] [Group K] [IsSimpleGroup K]
    (hKnc : ∃ a b : K, a * b ≠ b * a) (φ : Y →* K) (hφ : Function.Surjective φ) :
    ¬ Group.IsSolvable Y := fun hs => by
  have : Group.IsSolvable K := Group.isSolvable_of_surjective hφ
  obtain ⟨a, b, hab⟩ := hKnc
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr this) a b)

end CFSG.AGLEmbedding.CenterOver
