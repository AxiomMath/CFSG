module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem center_eq_bot_of_isSimpleGroup_nonabelian {L : Type*} [Group L] [IsSimpleGroup L]
    (h : ∃ a b : L, a * b ≠ b * a) : Subgroup.center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have : a ∈ Subgroup.center L := by rw [h1]; trivial
    exact hab (Subgroup.mem_center_iff.1 this b).symm

theorem card_dvd_of_central_extension {KC Q L : Type*} [Group KC] [Finite KC] [Group Q] [Group L]
    [Finite L] [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a)
    (e : KC ⧸ Subgroup.center KC ≃* Q) (A : Subgroup KC) (f : A →* L)
    (hf : Function.Surjective f) : Nat.card L ∣ Nat.card Q := by
  let π : A →* KC ⧸ Subgroup.center KC := (QuotientGroup.mk' (Subgroup.center KC)).comp A.subtype
  have hker : π.ker ≤ f.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    have hc : (a : KC) ∈ Subgroup.center KC := by
      simpa [π, QuotientGroup.eq_one_iff] using ha
    have hfa : f a ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨b, rfl⟩ := hf y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hc b
    rwa [center_eq_bot_of_isSimpleGroup_nonabelian hnab, Subgroup.mem_bot] at hfa
  let g : A ⧸ π.ker →* L := QuotientGroup.lift π.ker f hker
  have hg : Function.Surjective g := fun y => by
    obtain ⟨a, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk a, rfl⟩
  have h1 : Nat.card L ∣ Nat.card (A ⧸ π.ker) := Subgroup.card_dvd_of_surjective (f := g) hg
  have h2 : Nat.card (A ⧸ π.ker) = Nat.card π.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv
  have h3 : Nat.card π.range ∣ Nat.card (KC ⧸ Subgroup.center KC) :=
    Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_congr e.toEquiv] at h3
  exact h1.trans (h2 ▸ h3)

theorem card_sylow_eq_pow_of_card_eq {G : Type*} [Group G] [Finite G] {p k m : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m) (S : Sylow p G) :
    Nat.card (S : Subgroup G) = p ^ k := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hp : p.Prime := Fact.out
  rw [S.card_eq_multiplicity, hcard, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0,
    Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem isCyclic_sylow_of_orderOf_eq_pow {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    {g : G} (hg : orderOf g = p ^ k) (hS : ∀ S : Sylow p G, Nat.card (S : Subgroup G) = p ^ k)
    (P : Sylow p G) : IsCyclic (P : Subgroup G) := by
  have hQ : IsPGroup p (Subgroup.zpowers g) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hg]
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P' P
  have hgP' : g ∈ (P' : Subgroup G) := hP' (Subgroup.mem_zpowers g)
  have hx : c * g * c⁻¹ ∈ (P : Subgroup G) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul g (MulAut.conj c) (P' : Subgroup G) hgP'
  have hord : orderOf (⟨c * g * c⁻¹, hx⟩ : (P : Subgroup G)) = Nat.card (P : Subgroup G) := by
    have h1 : orderOf (c * g * c⁻¹) = orderOf g := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective g
      simpa [MulAut.conj_apply] using this
    rw [Subgroup.orderOf_mk, hS P, h1, hg]
  exact isCyclic_of_orderOf_eq_card _ hord

theorem isCyclic_sylow_three_of_card_three {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hcard : Nat.card G = 3 * m) (hm : ¬ 3 ∣ m) (P : Sylow 3 G) : IsCyclic (P : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := card_sylow_eq_pow_of_card_eq (k := 1) (by simpa using hcard) hm P
  exact isCyclic_of_prime_card (by simpa using h)

theorem isCyclic_sylow_three_of_orderOf_nine {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hcard : Nat.card G = 9 * m) (hm : ¬ 3 ∣ m) {g : G} (hg : orderOf g = 9) (P : Sylow 3 G) :
    IsCyclic (P : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isCyclic_sylow_of_orderOf_eq_pow (k := 2) (by simpa using hg)
    (card_sylow_eq_pow_of_card_eq (by simpa using hcard) hm) P

theorem pRank_le_pRank_mulAut_of_nonabelian {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ∃ a b : L, a * b ≠ b * a) {p k : ℕ} (hp : 1 < p)
    (hk : k ≤ pRank p (⊤ : Subgroup L)) : k ≤ pRank p (⊤ : Subgroup (MulAut L)) := by
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ : MulAut L => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rwa [center_eq_bot_of_isSimpleGroup_nonabelian hnab, Subgroup.mem_bot] at hc
  exact hk.trans (CFSG.SectionRank.pRank_top_le_of_injective hp (MulAut.conj : L →* MulAut L) hinj)

end CFSG.AGLEmbedding
