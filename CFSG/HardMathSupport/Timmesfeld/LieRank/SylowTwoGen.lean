module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SylowCore
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.UpperBound

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.HardMathSupport.Timmesfeld.SporadicRank

section

variable {X : Type} [Group X]

theorem mem_normalizer_of_pow_three {S : Subgroup X} {g : X} (hg : g ^ 3 = 1)
    (h : ∀ u ∈ S, g * u * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun u => ⟨h u, fun hu => ?_⟩
  have h3 : g * g * g = 1 := by simpa [pow_succ, mul_assoc] using hg
  have e : u = g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ := by
    calc u = (g * g * g) * u * (g * g * g)⁻¹ := by rw [h3]; simp
      _ = g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ := by group
  rw [e]
  exact h _ (h _ hu)

end

section

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_of_two_gens (D : ModuleSpec X 3) {xa xb : X}
    {Ma Mb : Matrix (Fin D.n) (Fin D.n) (ZMod 3)} (hMa : ActsBy D xa Ma) (hMb : ActsBy D xb Mb)
    (hxa : xa ^ 3 = 1) (hxb : xb ^ 3 = 1)
    (hc : ∀ i : Fin 3, ∃ c ∈ D.span, xb * xa ^ i.val = xa ^ i.val * xb * c)
    (hd : ∀ a b : Fin 9, a ≠ b →
      Ma ^ (a.val / 3) * Mb ^ (a.val % 3) ≠ Ma ^ (b.val / 3) * Mb ^ (b.val % 3)) :
    ∃ P : Subgroup X, D.span ≤ P ∧ xa ∈ P ∧ xb ∈ P ∧ Nat.card P = 3 ^ (D.n + 2) ∧
      P ≤ Subgroup.normalizer (D.span : Set X) ∧
      ∀ x ∈ P, (∀ a ∈ D.span, x * a = a * x) → x ∈ D.span := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set N : Subgroup X := Subgroup.normalizer (D.span : Set X) with hNdef
  have hconj : ∀ {g : X} {A : Matrix (Fin D.n) (Fin D.n) (ZMod 3)}, ActsBy D g A →
      ∀ u ∈ D.span, g * u * g⁻¹ ∈ D.span := by
    intro g A hg u hu
    obtain ⟨c, rfl⟩ := D.exists_elt hu
    rw [conj_elt D hg]
    exact D.elt_mem _
  have hxaN : xa ∈ N := mem_normalizer_of_pow_three hxa (hconj hMa)
  have hxbN : xb ∈ N := mem_normalizer_of_pow_three hxb (hconj hMb)
  have hspanN : D.span ≤ N := Subgroup.le_normalizer_iff.mpr fun h hh k hk =>
    mul_mem (mul_mem hh hk) (inv_mem hh)
  have hcN : ∀ {g : X}, g ∈ N → ∀ {u : X}, u ∈ D.span → g * u * g⁻¹ ∈ D.span := fun hg u hu =>
    ((Subgroup.mem_normalizer_iff.mp hg) u).mp hu
  let gens : Set X := {xa, xb} ∪ Set.range D.a
  let P : Subgroup X := Subgroup.closure gens
  have hxaP : xa ∈ P := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hxbP : xb ∈ P := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hspanP : D.span ≤ P := by
    rw [ModuleSpec.span, Subgroup.closure_le]
    exact fun u hu => Subgroup.subset_closure (Or.inr hu)
  have hPN : P ≤ N := by
    rw [Subgroup.closure_le]
    rintro x ((rfl | rfl) | ⟨k, rfl⟩)
    · exact hxaN
    · exact hxbN
    · exact hspanN (D.a_mem_span k)
  let S : Set X := {x | ∃ i j : ℕ, ∃ α ∈ D.span, x = xa ^ i * xb ^ j * α}
  have hPS : ∀ x ∈ P, x ∈ S := by
    intro x hx
    have hS1 : (1 : X) ∈ S := ⟨0, 0, 1, D.span.one_mem, by simp⟩
    have hSa : ∀ y ∈ S, xa * y ∈ S := by
      rintro y ⟨i, j, α, hα, rfl⟩
      exact ⟨i + 1, j, α, hα, by rw [pow_succ']; group⟩
    have hSb : ∀ y ∈ S, xb * y ∈ S := by
      rintro y ⟨i, j, α, hα, rfl⟩
      obtain ⟨c, hcs, hcc⟩ := hc ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩
      have hxj : xb ^ j ∈ N := N.pow_mem hxbN j
      have hc' : (xb ^ j)⁻¹ * c * xb ^ j ∈ D.span := by
        have := hcN (N.inv_mem hxj) hcs
        simpa using this
      refine ⟨i % 3, j + 1, (xb ^ j)⁻¹ * c * xb ^ j * α, D.span.mul_mem hc' hα, ?_⟩
      have hi : xa ^ i = xa ^ (i % 3) := pow_eq_pow_mod i hxa
      rw [hi]
      simp only at hcc
      calc xb * (xa ^ (i % 3) * xb ^ j * α)
          = (xb * xa ^ (i % 3)) * xb ^ j * α := by group
        _ = (xa ^ (i % 3) * xb * c) * xb ^ j * α := by rw [hcc]
        _ = xa ^ (i % 3) * xb ^ (j + 1) * ((xb ^ j)⁻¹ * c * xb ^ j * α) := by
            rw [pow_succ']; group
    have hSgen : ∀ k : Fin D.n, ∀ y ∈ S, D.a k * y ∈ S := by
      rintro k y ⟨i, j, α, hα, rfl⟩
      have hg : xa ^ i * xb ^ j ∈ N := N.mul_mem (N.pow_mem hxaN i) (N.pow_mem hxbN j)
      have h1 : (xa ^ i * xb ^ j)⁻¹ * D.a k * (xa ^ i * xb ^ j) ∈ D.span := by
        have := hcN (N.inv_mem hg) (D.a_mem_span k)
        simpa using this
      refine ⟨i, j, _, D.span.mul_mem h1 hα, ?_⟩
      group
    have hmul : ∀ z ∈ gens, ∀ y ∈ S, z * y ∈ S := by
      rintro z ((rfl | rfl) | ⟨k, rfl⟩) y hy
      · exact hSa y hy
      · exact hSb y hy
      · exact hSgen k y hy
    have hmulinv : ∀ z ∈ gens, ∀ y ∈ S, z⁻¹ * y ∈ S := by
      intro z hz y hy
      have hz3 : z ^ 3 = 1 := by
        rcases hz with (rfl | rfl) | ⟨k, rfl⟩
        · exact hxa
        · exact hxb
        · exact D.pow k
      have : z⁻¹ = z * z := by
        rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, ← pow_succ, hz3]
      rw [this, mul_assoc]
      exact hmul z hz _ (hmul z hz y hy)
    exact Subgroup.closure_induction_left (p := fun x _ => x ∈ S) hS1
      (fun z hz y _ hy => hmul z hz y hy) (fun z hz y _ hy => hmulinv z hz y hy) hx
  have hspn : Nat.card D.span = 3 ^ D.n := D.card_span hp
  have hup : Nat.card P ≤ 3 * 3 * Nat.card D.span := by
    let F : Fin 3 × Fin 3 × D.span → P := fun t =>
      ⟨xa ^ t.1.val * xb ^ t.2.1.val * (t.2.2 : X),
        P.mul_mem (P.mul_mem (P.pow_mem hxaP _) (P.pow_mem hxbP _)) (hspanP t.2.2.2)⟩
    have hF : Function.Surjective F := by
      rintro ⟨x, hx⟩
      obtain ⟨i, j, α, hα, rfl⟩ := hPS x hx
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨α, hα⟩), Subtype.ext ?_⟩
      show xa ^ (i % 3) * xb ^ (j % 3) * α = xa ^ i * xb ^ j * α
      rw [← pow_eq_pow_mod i hxa, ← pow_eq_pow_mod j hxb]
    calc Nat.card P ≤ Nat.card (Fin 3 × Fin 3 × D.span) := Nat.card_le_card_of_surjective F hF
      _ = 3 * 3 * Nat.card D.span := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
        ring
  let g : Fin 9 → X := fun n => xa ^ (n.val / 3) * xb ^ (n.val % 3)
  let A : Fin 9 → Matrix (Fin D.n) (Fin D.n) (ZMod 3) := fun n =>
    Ma ^ (n.val / 3) * Mb ^ (n.val % 3)
  have hg : ∀ n, g n ∈ P := fun n => P.mul_mem (P.pow_mem hxaP _) (P.pow_mem hxbP _)
  have hA : ∀ n, ActsBy D (g n) (A n) := fun n =>
    actsBy_mul D (actsBy_pow D hMa _) (actsBy_pow D hMb _)
  have hlow : 9 * Nat.card D.span ≤ Nat.card P := card_ge_of_actsBy D P hspanP g A hg hA hd
  have hcard : Nat.card P = 3 ^ (D.n + 2) := by
    have : Nat.card P = 9 * Nat.card D.span := le_antisymm (by simpa using hup) hlow
    rw [this, hspn, pow_add]
    ring
  set C : Subgroup X := P ⊓ Subgroup.centralizer (D.span : Set X) with hCdef
  have hCc : ∀ x ∈ C, ∀ i, x * D.a i = D.a i * x := fun x hx i =>
    (Subgroup.mem_centralizer_iff.mp hx.2 (D.a i) (D.a_mem_span i)).symm
  have hspanC : D.span ≤ C := fun x hx =>
    ⟨hspanP hx, Subgroup.mem_centralizer_iff.mpr fun h hh => D.mul_comm_of_mem hh hx⟩
  have hCle := card_mul_le_of_actsBy D P C inf_le_left hCc g A hg hA hd
  have hCeq : D.span = C := by
    refine Subgroup.eq_of_le_of_card_ge hspanC ?_
    have : 9 * Nat.card C ≤ 9 * Nat.card D.span := by
      calc 9 * Nat.card C ≤ Nat.card P := hCle
        _ = 9 * Nat.card D.span := le_antisymm (by simpa using hup) hlow
    omega
  refine ⟨P, hspanP, hxaP, hxbP, hcard, hPN, fun x hx hxc => ?_⟩
  rw [hCeq]
  exact ⟨hx, Subgroup.mem_centralizer_iff.mpr fun h hh => (hxc h hh).symm⟩

omit [Finite X] in
theorem card_fixed_le_of_two (D : ModuleSpec X 3) {xa xb : X}
    {Ma Mb : Matrix (Fin D.n) (Fin D.n) (ZMod 3)} (hMa : ActsBy D xa Ma) (hMb : ActsBy D xb Mb)
    (P : Subgroup X) (hxa : xa ∈ P) (hxb : xb ∈ P) :
    Nat.card ↥(D.span ⊓ Subgroup.centralizer (P : Set X)) ≤
      Nat.card {c : Fin D.n → ZMod 3 // Ma.mulVec c = c ∧ Mb.mulVec c = c} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfix : ∀ {g : X} {A : Matrix (Fin D.n) (Fin D.n) (ZMod 3)}, ActsBy D g A → g ∈ P →
      ∀ a : ↥(D.span ⊓ Subgroup.centralizer (P : Set X)),
        A.mulVec (Classical.choose (D.exists_elt a.2.1)) =
          Classical.choose (D.exists_elt a.2.1) := by
    intro g A hg hgP a
    have hc := Classical.choose_spec (D.exists_elt a.2.1)
    have h1 : g * (a : X) = (a : X) * g := Subgroup.mem_centralizer_iff.mp a.2.2 g hgP
    apply D.elt_injective
    rw [← conj_elt D hg, hc, h1]
    group
  let ι : ↥(D.span ⊓ Subgroup.centralizer (P : Set X)) →
      {c : Fin D.n → ZMod 3 // Ma.mulVec c = c ∧ Mb.mulVec c = c} := fun a =>
    ⟨Classical.choose (D.exists_elt a.2.1), hfix hMa hxa a, hfix hMb hxb a⟩
  refine Nat.card_le_card_of_injective ι fun a b hab => ?_
  have h := congrArg Subtype.val hab
  apply Subtype.ext
  rw [← Classical.choose_spec (D.exists_elt a.2.1), ← Classical.choose_spec (D.exists_elt b.2.1)]
  exact congrArg D.elt h

theorem pRank_le_of_two_gens (D : ModuleSpec X 3) {xa xb : X}
    {Ma Mb : Matrix (Fin D.n) (Fin D.n) (ZMod 3)} (hMa : ActsBy D xa Ma) (hMb : ActsBy D xb Mb)
    (hxa : xa ^ 3 = 1) (hxb : xb ^ 3 = 1)
    (hc : ∀ i : Fin 3, ∃ c ∈ D.span, xb * xa ^ i.val = xa ^ i.val * xb * c)
    (hd : ∀ a b : Fin 9, a ≠ b →
      Ma ^ (a.val / 3) * Mb ^ (a.val % 3) ≠ Ma ^ (b.val / 3) * Mb ^ (b.val % 3))
    {z r : ℕ} (hord : (Nat.card X).factorization 3 = D.n + 2)
    (hfix : Nat.card {c : Fin D.n → ZMod 3 // Ma.mulVec c = c ∧ Mb.mulVec c = c} ≤ 3 ^ z)
    (hnum : ∀ a j, a ≤ D.n → j ≤ 2 → (0 < j → a < D.n) → (j = 2 → a ≤ z) → a + j ≤ r) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ r := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨P, hspanP, hxaP, hxbP, hPcard, hPN, hcen⟩ :=
    exists_sylow_of_two_gens D hMa hMb hxa hxb hc hd
  have hAc : ∀ a ∈ D.span, ∀ b ∈ D.span, a * b = b * a := fun a ha b hb =>
    D.mul_comm_of_mem ha hb
  have hz : Nat.card ↥(D.span ⊓ Subgroup.centralizer (P : Set X)) ≤ 3 ^ z :=
    (card_fixed_le_of_two D hMa hMb P hxaP hxbP).trans hfix
  refine pRank_le_of_sylow hp P (by rw [hPcard, hord]) (k := r) fun E hEP hE => ?_
  obtain ⟨a, j, hcard, ha, hj, h1, h2⟩ := card_elemAbelian_le_of_setup hp D.span P hspanP hPN
    hAc hcen (D.card_span hp) hPcard hz E hEP fun x hx y hy => by
      have := hE.1
      exact mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩ |> congrArg Subtype.val
  rw [hcard]
  exact Nat.pow_le_pow_right hp.pos (hnum a j ha hj h1 h2)

end

end CFSG.HardMathSupport.Timmesfeld.LieRank
