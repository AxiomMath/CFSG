module

public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem sl2Three_exists_cubes : ∀ g : SL(2, ZMod 3), ∃ a b c : SL(2, ZMod 3),
    a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ g = a * b * c := by
  decide +kernel

theorem sl2Three_exists_conj : ∀ x y : SL(2, ZMod 3), x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 →
    y = 1 ∨ ∃ g : SL(2, ZMod 3), y = g * x * g⁻¹ ∨ y = g * x⁻¹ * g⁻¹ := by
  decide +kernel

section Iso

theorem eq_top_of_normal_of_pow_three {B : Type*} [Group B] (eB : SL(2, ZMod 3) ≃* B)
    {N : Subgroup B} (hN : ∀ x ∈ N, ∀ g : B, g * x * g⁻¹ ∈ N) {x : B} (hx : x ∈ N)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : N = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, b, c, ha, hb, hc, hg⟩ := sl2Three_exists_cubes (eB.symm g)
  have hx3' : (eB.symm x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hx1' : eB.symm x ≠ 1 := fun h => hx1 (by simpa using congrArg eB h)
  have key : ∀ y : SL(2, ZMod 3), y ^ 3 = 1 → eB y ∈ N := by
    intro y hy
    rcases sl2Three_exists_conj (eB.symm x) y hx3' hx1' hy with rfl | ⟨h, rfl | rfl⟩
    · simp
    · simpa using hN x hx (eB h)
    · simpa using hN x⁻¹ (N.inv_mem hx) (eB h)
  have hgeq : g = eB a * eB b * eB c := by
    rw [← map_mul, ← map_mul, ← hg]
    simp
  rw [hgeq]
  exact N.mul_mem (N.mul_mem (key a ha) (key b hb)) (key c hc)

private theorem isSubnormal_sl2Three_cases_aux {B : Type*} [Group B] (eB : SL(2, ZMod 3) ≃* B)
    {N T : Subgroup B} (h : IsSubnormal N T) (hT : T = ⊤) :
    N = ⊤ ∨ ∀ x ∈ N, x ^ 3 = 1 → x = 1 := by
  induction h with
  | refl H => exact Or.inl hT
  | @step H M K hHM hN hMK ih =>
    rcases ih hT with hM | hM
    · by_cases hex : ∃ x ∈ H, x ^ 3 = 1 ∧ x ≠ 1
      · obtain ⟨x, hxH, hx3, hx1⟩ := hex
        refine Or.inl (eq_top_of_normal_of_pow_three eB (fun y hy g => ?_) hxH hx3 hx1)
        exact (Subgroup.normal_subgroupOf_iff hHM).mp hN y g hy (hM ▸ Subgroup.mem_top g)
      · push Not at hex
        exact Or.inr hex
    · exact Or.inr fun x hx => hM x (hHM hx)

theorem isSubnormal_sl2Three_cases {B : Type*} [Group B] (eB : SL(2, ZMod 3) ≃* B)
    {N : Subgroup B} (h : IsSubnormal N ⊤) : N = ⊤ ∨ ∀ x ∈ N, x ^ 3 = 1 → x = 1 :=
  isSubnormal_sl2Three_cases_aux eB h rfl

end Iso

theorem false_of_isQuasisimple_of_isSolvable {B : Type*} [Group B]
    (hq : CFSG.Open.IsQuasisimple B) (hs : Group.IsSolvable B) : False := by
  have : Nontrivial (B ⧸ Subgroup.center B) := hq.2.toNontrivial
  have : Nontrivial B := (QuotientGroup.mk'_surjective (Subgroup.center B)).nontrivial
  have : Group.IsPerfect B := ⟨hq.1⟩
  exact Group.IsPerfect.not_isSolvable B hs

section Product

theorem snd_eq_one_of_isSubnormal_prod {A B : Type*} [Group A] [Group B] {L : Subgroup (A × B)}
    (e : SL(2, ZMod 3) ≃* L) (hsub : IsSubnormal L ⊤)
    (hB : Subsingleton B ∨ (CFSG.Open.IsQuasisimple B ∧ IsPGroup 2 (Subgroup.center B)) ∨
      Nonempty (SL(2, ZMod 3) ≃* B))
    {z : A × B} (hzL : z ∈ L) (hz1 : z ≠ 1) (hz2 : z.2 = 1) : ∀ x ∈ L, x.2 = 1 := by
  have hSsub : IsSubnormal (L.map (MonoidHom.snd A B)) ⊤ := by
    have := CFSG.ComponentClassification.Components.chain_map (MonoidHom.snd A B) hsub
    rwa [Subgroup.map_top_of_surjective _ Prod.snd_surjective] at this
  have hLsolv : Group.IsSolvable L :=
    haveI := isSolvable_sl2Three
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hsurj : L.map (MonoidHom.snd A B) = ⊤ → Function.Surjective
      ((MonoidHom.snd A B).comp L.subtype) := fun htop b => by
    obtain ⟨x, hx, rfl⟩ : b ∈ L.map (MonoidHom.snd A B) := htop ▸ Subgroup.mem_top b
    exact ⟨⟨x, hx⟩, rfl⟩
  have key : ∀ c ∈ L, c ^ 3 = 1 → c.2 = 1 := by
    intro c hc hc3
    have hb3 : c.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hc3
    have hbS : c.2 ∈ L.map (MonoidHom.snd A B) := ⟨c, hc, rfl⟩
    rcases hB with hsing | ⟨hqs, hZ⟩ | ⟨⟨eB⟩⟩
    · exact Subsingleton.elim _ _
    · rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hqs _ hSsub
        with hle | htop
      · have hz : c.2 ∈ Subgroup.center B := hle hbS
        have hdvd : orderOf (⟨c.2, hz⟩ : Subgroup.center B) ∣ 3 :=
          orderOf_dvd_of_pow_eq_one (Subtype.ext hb3)
        obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ ⟨c.2, hz⟩
        have hk0 : k = 0 := by
          by_contra hne
          rw [hk] at hdvd
          exact absurd ((dvd_pow_self 2 hne).trans hdvd) (by norm_num)
        rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
        exact congrArg Subtype.val hk
      · exact (false_of_isQuasisimple_of_isSolvable hqs
          (Group.isSolvable_of_surjective (hsurj htop))).elim
    · rcases isSubnormal_sl2Three_cases eB hSsub with htop | hno
      · exfalso
        have : Finite L := Finite.of_equiv _ e.toEquiv
        have hcard : Nat.card L ≤ Nat.card B := by
          rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr eB.toEquiv]
        have hbij := (hsurj htop).bijective_of_nat_card_le hcard
        have h1 := hbij.1 (a₁ := ⟨z, hzL⟩) (a₂ := 1) (by simpa using hz2)
        exact hz1 (congrArg Subtype.val h1)
      · exact hno c.2 hbS hb3
  intro x hx
  obtain ⟨g, hg⟩ := e.surjective ⟨x, hx⟩
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := sl2Three_exists_cubes g
  have hcube : ∀ y : SL(2, ZMod 3), y ^ 3 = 1 → ((e y : L) : A × B).2 = 1 := fun y hy =>
    key _ (e y).2 (by rw [← Subgroup.coe_pow, ← map_pow, hy, map_one]; rfl)
  have hx' : x = ((e a : L) : A × B) * (e b : L) * (e c : L) := by
    have := congrArg Subtype.val hg
    rw [map_mul, map_mul] at this
    exact this.symm
  rw [hx', Prod.snd_mul, Prod.snd_mul, hcube a ha, hcube b hb, hcube c hc]
  simp

end Product

section Subgroups

variable {G : Type*} [Group G]

theorem le_of_isSubnormal_of_commute {A B L : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (e : SL(2, ZMod 3) ≃* L) (hLle : L ≤ A ⊔ B) (hsub : IsSubnormal L (A ⊔ B))
    (hB : Subsingleton B ∨ (CFSG.Open.IsQuasisimple B ∧ IsPGroup 2 (Subgroup.center B)) ∨
      Nonempty (SL(2, ZMod 3) ≃* B))
    {z : G} (hzL : z ∈ L) (hz1 : z ≠ 1) (hzA : z ∈ A) : L ≤ A := by
  have hcomm' : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  let Φ : A × B →* G := A.subtype.noncommCoprod B.subtype hcomm'
  have hΦapp : ∀ p : A × B, Φ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hinj : Function.Injective Φ := by
    refine (MonoidHom.noncommCoprod_injective _ _ hcomm').mpr
      ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.mpr hinf
  have hrange : Φ.range = A ⊔ B := by
    rw [show Φ.range = A.subtype.range ⊔ B.subtype.range from
      MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm', Subgroup.range_subtype,
      Subgroup.range_subtype]
  have hLrange : L ≤ Φ.range := hrange ▸ hLle
  have hL'sub : IsSubnormal (L.comap Φ) ⊤ := by
    have h1 := ModelFacts.isSubnormal_comap Φ hsub
    have htop : (A ⊔ B).comap Φ = ⊤ := eq_top_iff.mpr fun p _ => by
      show Φ p ∈ A ⊔ B
      rw [← hrange]
      exact ⟨p, rfl⟩
    rwa [htop] at h1
  let eL : ↥(L.comap Φ) ≃* ↥L := (Subgroup.equivMapOfInjective (L.comap Φ) Φ hinj).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLrange))
  have hp0L : ((⟨z, hzA⟩ : A), (1 : B)) ∈ L.comap Φ := by
    show Φ _ ∈ L
    rw [hΦapp]
    simpa using hzL
  have hp01 : ((⟨z, hzA⟩ : A), (1 : B)) ≠ 1 := fun h => hz1 (by
    simpa using congrArg (fun p : A × B => (p.1 : G)) h)
  have hall := snd_eq_one_of_isSubnormal_prod (e.trans eL.symm) hL'sub hB hp0L hp01 rfl
  intro x hx
  obtain ⟨q, hq⟩ := hLrange hx
  have hqL : q ∈ L.comap Φ := by
    show Φ q ∈ L
    rw [hq]
    exact hx
  have h2 : q.2 = 1 := hall q hqL
  have hxq : x = (q.1 : G) := by
    rw [← hq, hΦapp, h2, Subgroup.coe_one, mul_one]
  rw [hxq]
  exact q.1.2

theorem not_isQuasisimple_of_member3 {A L : Subgroup G} (e : SL(2, ZMod 3) ≃* L) (hLA : L ≤ A)
    (hsub : IsSubnormal L A) : ¬ CFSG.Open.IsQuasisimple A := by
  intro hq
  have hsub' : IsSubnormal (L.subgroupOf A) ⊤ := by
    have := isSubnormal_subgroupOf hsub A
    rwa [Subgroup.subgroupOf_self] at this
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hq _ hsub' with
    hle | htop
  · refine sl2Three_not_comm fun a b => e.injective ?_
    rw [map_mul, map_mul]
    apply Subtype.ext
    have h1 := Subgroup.mem_center_iff.mp (hle (show (⟨(e a : G), hLA (e a).2⟩ : A) ∈
      L.subgroupOf A from (e a).2)) ⟨(e b : G), hLA (e b).2⟩
    simpa using (congrArg (fun t : A => (t : G)) h1).symm
  · have hAL : A ≤ L := fun x hx => by
      have : (⟨x, hx⟩ : A) ∈ L.subgroupOf A := htop ▸ Subgroup.mem_top _
      exact this
    have hAeq : L = A := le_antisymm hLA hAL
    subst hAeq
    have hsolv : Group.IsSolvable L :=
      haveI := isSolvable_sl2Three
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact false_of_isQuasisimple_of_isSolvable hq hsolv

theorem eq_of_le_of_natCard_le {A L : Subgroup G} [Finite A] (e : SL(2, ZMod 3) ≃* L)
    (hLA : L ≤ A) (hA : Nat.card A ≤ 24) : L = A :=
  Subgroup.eq_of_le_of_card_ge hLA (by rw [← Nat.card_congr e.toEquiv, natCard_sl2Three]; exact hA)

end Subgroups

end CFSG.ClassicalInvolution.Q3
