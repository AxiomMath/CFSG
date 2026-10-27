module

public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Levi

variable {G : Type*} [Group G]

theorem exists_levi_hom [Finite G] {P Q M L : Subgroup G} (hQP : Q ≤ P)
    (hN : P ≤ Subgroup.normalizer (Q : Set G)) (hQM : Q ⊓ M = ⊥) (hP : Q ⊔ M = P)
    (hLM : L ≤ M) (hL : ⁅L, L⁆ = L) (hM : perfectCore M ≤ L) :
    ∃ g : ↥(perfectCore P) →* ↥L, Function.Surjective g ∧ ∀ x, g x = 1 → (x : G) ∈ Q := by
  have hMP : M ≤ P := hP ▸ le_sup_right
  have hnorm : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hN
  let ψ : ↥M →* ↥P ⧸ Q.subgroupOf P :=
    (QuotientGroup.mk' (Q.subgroupOf P)).comp (Subgroup.inclusion hMP)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have h1 : Subgroup.inclusion hMP m ∈ Q.subgroupOf P :=
      (QuotientGroup.eq_one_iff _).mp hm
    have h2 : (m : G) ∈ Q ⊓ M := ⟨h1, m.2⟩
    rw [hQM, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    exact Subtype.ext h2
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective y
    have hp : (p : G) ∈ ((M ⊔ Q : Subgroup G) : Set G) := by
      rw [sup_comm, hP]
      exact p.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M Q (hMP.trans hN)] at hp
    obtain ⟨m, hm, q, hq, hpmq⟩ := hp
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((Subgroup.inclusion hMP ⟨m, hm⟩)⁻¹ * p : ↥P) : G) = q := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hpmq]
      simp
    rw [this]
    exact hq
  let e : ↥M ≃* (↥P ⧸ Q.subgroupOf P) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  let lev : ↥P →* ↥M := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf P))
  have hlev_M : ∀ (m : G) (hm : m ∈ M), lev ⟨m, hMP hm⟩ = ⟨m, hm⟩ := by
    intro m hm
    show e.symm (QuotientGroup.mk' (Q.subgroupOf P) ⟨m, hMP hm⟩) = ⟨m, hm⟩
    rw [MulEquiv.symm_apply_eq]
    rfl
  have hlev_ker : ∀ p : ↥P, lev p = 1 → (p : G) ∈ Q := by
    intro p hp
    have hp' : e.symm (QuotientGroup.mk' (Q.subgroupOf P) p) = 1 := hp
    have h1 : QuotientGroup.mk' (Q.subgroupOf P) p = e 1 := (MulEquiv.symm_apply_eq e).mp hp'
    rw [map_one] at h1
    have h2 := (QuotientGroup.eq_one_iff (N := Q.subgroupOf P) p).mp h1
    exact h2
  have hPcore : Group.IsPerfect ↥(perfectCore P) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect P)
  let ι : ↥(perfectCore P) →* ↥P := Subgroup.inclusion (perfectCore_le P)
  let f : ↥(perfectCore P) →* G := M.subtype.comp (lev.comp ι)
  have hrperf : ⁅f.range, f.range⁆ = f.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)
  have hrM : f.range ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact (lev (ι x)).2
  have hrL : f.range ≤ L := (le_perfectCore_of_perfect hrM hrperf).trans hM
  refine ⟨f.codRestrict L fun x => hrL ⟨x, rfl⟩, ?_, ?_⟩
  · intro l
    have hlP : (l : G) ∈ perfectCore P := le_perfectCore_of_perfect (hLM.trans hMP) hL l.2
    refine ⟨⟨l, hlP⟩, Subtype.ext ?_⟩
    have h1 := congrArg (fun m : ↥M => (m : G)) (hlev_M l (hLM l.2))
    exact h1
  · intro x hx
    have h1 : ((lev (ι x) : ↥M) : G) = 1 := congrArg Subtype.val hx
    exact hlev_ker _ (Subtype.ext h1)

theorem perfectCore_map_subgroupOf [Finite G] {C P : Subgroup G} (hPC : P ≤ C) :
    (perfectCore (P.subgroupOf C)).map C.subtype = perfectCore P := by
  rw [map_perfectCore C.subtype (P.subgroupOf C), Subgroup.map_subgroupOf_eq_of_le hPC]

theorem exists_levi_hom_subgroupOf [Finite G] {C P Q M L : Subgroup G} (hPC : P ≤ C) (hQP : Q ≤ P)
    (hN : P ≤ Subgroup.normalizer (Q : Set G)) (hQM : Q ⊓ M = ⊥) (hP : Q ⊔ M = P)
    (hLM : L ≤ M) (hL : ⁅L, L⁆ = L) (hM : perfectCore M ≤ L) :
    ∃ g : ↥(perfectCore (P.subgroupOf C)) →* ↥L, Function.Surjective g ∧
      ∀ x, g x = 1 → (((x : ↥C)) : G) ∈ Q := by
  obtain ⟨g, hg, hk⟩ := exists_levi_hom hQP hN hQM hP hLM hL hM
  have hmap := perfectCore_map_subgroupOf hPC
  let h : ↥(perfectCore (P.subgroupOf C)) →* ↥(perfectCore P) :=
    (C.subtype.comp (perfectCore (P.subgroupOf C)).subtype).codRestrict (perfectCore P) (fun x => by
      rw [← hmap]
      exact ⟨x.1, x.2, rfl⟩)
  have hsurj : Function.Surjective h := by
    intro y
    have hy : (y : G) ∈ (perfectCore (P.subgroupOf C)).map C.subtype := by
      rw [hmap]
      exact y.2
    obtain ⟨c, hc, hcy⟩ := hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  exact ⟨g.comp h, hg.comp hsurj, fun x hx => hk (h x) hx⟩

theorem isPGroup_ker_of_levi {p : ℕ} [Fact p.Prime] {C Q : Subgroup G} {Pc : Subgroup ↥C}
    (hQ : IsPGroup p ↥Q) {T : Type*} [Group T] (g : ↥Pc →* T)
    (hk : ∀ x, g x = 1 → (((x : ↥C)) : G) ∈ Q) : IsPGroup p g.ker := by
  let φ : ↥g.ker →* ↥Q :=
    ((C.subtype.comp Pc.subtype).comp g.ker.subtype).codRestrict Q fun x => hk x.1 x.2
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  exact IsPGroup.of_injective hQ φ hinj

end Levi

end CFSG.QuasithinUnique.Vol2Native.A312L
