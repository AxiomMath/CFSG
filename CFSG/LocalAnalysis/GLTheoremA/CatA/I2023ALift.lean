module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_lift {x : G} {L : Subgroup G} (hL : GLAPComponent 3 (cx x) L)
    (hXN : cx x ≤ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    {bs : G} (hbs : bs ∈ cx x) (hbs3 : bs ^ 3 ∈ GLAPPrimeCoreOf 3 (cx x))
    {D : Subgroup (PQuot 3 L)} (hD : IsElemAbelian 3 D)
    (hDfix : ∀ d ∈ D, rho L ⟨bs, hXN hbs⟩ d = d)
    {M : Subgroup (MulAut (PQuot 3 L))} (hMD : ∀ d ∈ D, MulAut.conj d ∈ M)
    (hMbs : rho L ⟨bs, hXN hbs⟩ ∈ M) :
    ∃ S : Subgroup G, S ≤ cx x ∧ IsElemAbelian 3 S ∧ x ∈ S ∧
      (∃ n ∈ GLAPPrimeCoreOf 3 (cx x), bs * n ∈ S) ∧
      (∀ l : ↥L, (QuotientGroup.mk l : PQuot 3 L) ∈ D →
        ∃ n ∈ GLAPPrimeCoreOf 3 (cx x), (l : G) * n ∈ S) ∧
      (∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set G), rho L ⟨s, hs⟩ ∈ M) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set X : Subgroup G := cx x with hX
  have hLX : L ≤ X := hL.1
  have hxX : x ∈ X := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxc : ∀ g ∈ X, g * x = x * g := fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg
  set Nn : Subgroup ↥X := GLAPPrimeCore 3 ↥X with hNn
  set π : ↥X →* ↥X ⧸ Nn := QuotientGroup.mk' Nn with hπ
  have hOL : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 X := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp3 hL.2.1]
    exact inf_le_right
  have hπeq : ∀ y z : ↥X, π y = π z ↔ (y : G)⁻¹ * (z : G) ∈ GLAPPrimeCoreOf 3 X :=
    fun y z => mk_eq_iff_X X y z
  have hπ1 : ∀ y : ↥X, π y = 1 ↔ (y : G) ∈ GLAPPrimeCoreOf 3 X := by
    intro y
    rw [← map_one π, hπeq]
    simp
  let lX : ↥L → ↥X := fun l => ⟨l, hLX l.2⟩
  let G₀ : Set (↥X ⧸ Nn) := {e | (∃ l : ↥L, (QuotientGroup.mk l : PQuot 3 L) ∈ D ∧ e = π (lX l)) ∨
    e = π ⟨x, hxX⟩ ∨ e = π ⟨bs, hbs⟩}
  have hcl : ∀ l l' : ↥L, (QuotientGroup.mk l : PQuot 3 L) ∈ D → (QuotientGroup.mk l' : PQuot 3 L) ∈ D →
      π (lX l) * π (lX l') = π (lX l') * π (lX l) := by
    intro l l' hl hl'
    rw [← map_mul, ← map_mul, hπeq]
    have h1 : (QuotientGroup.mk (l * l') : PQuot 3 L) = QuotientGroup.mk (l' * l) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hl⟩ ⟨_, hl'⟩)
    exact hOL ((mk_eq_iff L _ _).1 h1)
  have hcx : ∀ y : ↥X, π ⟨x, hxX⟩ * π y = π y * π ⟨x, hxX⟩ := by
    intro y
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hxc y y.2).symm)
  have hcb : ∀ l : ↥L, (QuotientGroup.mk l : PQuot 3 L) ∈ D →
      π (lX l) * π ⟨bs, hbs⟩ = π ⟨bs, hbs⟩ * π (lX l) := by
    intro l hl
    have h1 := hDfix _ hl
    have hy : bs * (l : G) * bs⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hXN hbs) l).1 l.2
    rw [rho_mk' L (hXN hbs) l ⟨bs * l * bs⁻¹, hy⟩ rfl] at h1
    have h2 := hOL ((mk_eq_iff L _ _).1 h1.symm)
    have h3 : π (⟨bs, hbs⟩ * lX l * ⟨bs, hbs⟩⁻¹) = π (lX l) :=
      ((hπeq _ _).2 (by simpa using h2)).symm
    rw [map_mul, map_mul, map_inv] at h3
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hl3 : ∀ l : ↥L, (QuotientGroup.mk l : PQuot 3 L) ∈ D → π (lX l) ^ 3 = 1 := by
    intro l hl
    have h1 : (QuotientGroup.mk (l ^ 3) : PQuot 3 L) = QuotientGroup.mk 1 := by
      rw [QuotientGroup.mk_pow, QuotientGroup.mk_one]
      exact hD.2 _ hl
    have h2 := hOL ((mk_eq_iff L _ _).1 h1)
    rw [← map_pow, hπ1]
    have h3 : (((lX l) ^ 3 : ↥X) : G) = ((l ^ 3 : ↥L) : G) := rfl
    rw [h3]
    simpa using Subgroup.inv_mem _ h2
  have hx3' : π ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow, hπ1]
    have : ((⟨x, hxX⟩ : ↥X) ^ 3 : ↥X) = 1 := Subtype.ext hx3
    rw [this]
    exact Subgroup.one_mem _
  have hb3' : π ⟨bs, hbs⟩ ^ 3 = 1 := by
    rw [← map_pow, hπ1]
    exact hbs3
  have hE : IsElemAbelian 3 (Subgroup.closure G₀) := by
    refine isElemAbelian_closure G₀ ?_ ?_
    · rintro a (⟨l, hl, rfl⟩ | rfl | rfl) b (⟨l', hl', rfl⟩ | rfl | rfl)
      · exact hcl l l' hl hl'
      · exact (hcx _).symm
      · exact hcb l hl
      · exact hcx _
      · rfl
      · exact hcx _
      · exact (hcb l' hl').symm
      · exact (hcx _).symm
      · rfl
    · rintro a (⟨l, hl, rfl⟩ | rfl | rfl)
      · exact hl3 l hl
      · exact hx3'
      · exact hb3'
  have hxE : π ⟨x, hxX⟩ ∈ Subgroup.closure G₀ := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hsec : ∀ e ∈ Subgroup.closure G₀, ∃ z : ↥X, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) z = e ∧
      (z : G) ∈ Subgroup.normalizer (L : Set G) := by
    intro e _
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Nn e
    exact ⟨z, rfl, hXN z.2⟩
  have hx3X : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext hx3
  obtain ⟨S₀, hS₀el, hxS₀, hcard, -, hsurj⟩ :=
    exists_elemAb_lift hL hE hsec ⟨x, hxX⟩ hx3X hxE
  have hEq : Subgroup.closure G₀ = S₀.map π := by
    have hle : Subgroup.closure G₀ ≤ S₀.map π := fun e he => by
      obtain ⟨s, hs, hse⟩ := hsurj e he
      exact ⟨s, hs, hse⟩
    haveI : Finite ↥(S₀.map π) := inferInstance
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← hcard]
    exact Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective S₀)
  let rhoX : ↥X →* MulAut (PQuot 3 L) := (rho L).comp (Subgroup.inclusion hXN)
  have hrhoX : ∀ z : ↥X, rhoX z = rho L ⟨(z : G), hXN z.2⟩ := fun z => rfl
  have hEPM : Subgroup.closure G₀ ≤ (M.comap rhoX).map π := by
    rw [Subgroup.closure_le]
    rintro e (⟨l, hl, rfl⟩ | rfl | rfl)
    · refine ⟨lX l, ?_, rfl⟩
      show rhoX (lX l) ∈ M
      rw [hrhoX]
      have := rho_inner L l
      exact (show rho L ⟨(l : G), hXN (hLX l.2)⟩ = MulAut.conj (QuotientGroup.mk l : PQuot 3 L) from
        this) ▸ hMD _ hl
    · refine ⟨⟨x, hxX⟩, ?_, rfl⟩
      show rhoX ⟨x, hxX⟩ ∈ M
      rw [hrhoX]
      have hxcent : x ∈ Subgroup.centralizer (L : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun l hl => hxc l (hLX hl)
      have h1 : rho L ⟨x, hXN hxX⟩ = 1 :=
        (rho_eq_one_iff L (hXN hxX)).2 (centMod_iff.1 (centMod_of_mem_centralizer hxcent))
      rw [h1]
      exact M.one_mem
    · exact ⟨⟨bs, hbs⟩, hMbs, rfl⟩
  refine ⟨S₀.map X.subtype, Subgroup.map_subtype_le _, isElemAbelian_map_inj X.subtype
    X.subtype_injective hS₀el, ⟨⟨x, hxX⟩, hxS₀, rfl⟩, ?_, ?_, ?_⟩
  ·
    have hbE : π ⟨bs, hbs⟩ ∈ Subgroup.closure G₀ := Subgroup.subset_closure (Or.inr (Or.inr rfl))
    obtain ⟨s, hs, hsb⟩ := hsurj _ hbE
    have h1 := (hπeq s ⟨bs, hbs⟩).1 hsb
    refine ⟨(bs)⁻¹ * (s : G), ?_, ?_⟩
    · have := Subgroup.inv_mem _ h1
      simpa using this
    · rw [mul_inv_cancel_left]
      exact ⟨s, hs, rfl⟩
  · intro l hl
    have hlE : π (lX l) ∈ Subgroup.closure G₀ := Subgroup.subset_closure (Or.inl ⟨l, hl, rfl⟩)
    obtain ⟨s, hs, hsl⟩ := hsurj _ hlE
    have h1 := (hπeq s (lX l)).1 hsl
    refine ⟨(l : G)⁻¹ * (s : G), ?_, ?_⟩
    · have := Subgroup.inv_mem _ h1
      simpa using this
    · rw [mul_inv_cancel_left]
      exact ⟨s, hs, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩ hs'
    have hsE : π s ∈ (M.comap rhoX).map π := hEPM (hEq ▸ ⟨s, hs, rfl⟩)
    obtain ⟨p, hp, hps⟩ := hsE
    have h1 := (hπeq p s).1 hps
    have h2 := rho_eq_of_inv_mul_mem hL (hXN p.2) hs' h1
    rw [h2]
    exact hp

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
