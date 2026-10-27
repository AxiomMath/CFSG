module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Simple
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Inner
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section CentralQuot

variable {Y Y' : Type*} [Group Y] [Group Y']

theorem mem_center_of_map_mem_center (f : Y →* Y') (hker : f.ker ≤ Subgroup.center Y)
    [Group.IsPerfect Y] {x : Y} (hx : f x ∈ Subgroup.center Y') : x ∈ Subgroup.center Y := by
  have hcen : ∀ y : Y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Y := by
    intro y
    apply hker
    rw [MonoidHom.mem_ker]
    have h := Subgroup.mem_center_iff.1 hx (f y)
    simp only [map_mul, map_inv]
    calc f x * f y * (f x)⁻¹ * (f y)⁻¹ = f y * f x * (f x)⁻¹ * (f y)⁻¹ := by rw [← h]
      _ = 1 := by group
  let c : Y →* Y := MonoidHom.mk' (fun y => x * y * x⁻¹ * y⁻¹) (by
    intro y z
    have hz := Subgroup.mem_center_iff.1 (hcen z) y
    calc x * (y * z) * x⁻¹ * (y * z)⁻¹
        = (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
      _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [hz]; group)
  have hc1 : ∀ a b : Y, c ⁅a, b⁆ = 1 := by
    intro a b
    rw [map_commutatorElement]
    exact (commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 (hcen a) (c b)).symm)
  have htop : (⊤ : Subgroup Y) ≤ c.ker := by
    have hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
      rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top (G := Y)
    rw [← hperf, Subgroup.commutator_le]
    intro a _ b _
    exact hc1 a b
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := htop (Subgroup.mem_top y)
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h1]; group

noncomputable def quotCenterEquivOfCentral (f : Y →* Y') (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center Y) [Group.IsPerfect Y] :
    (Y ⧸ Subgroup.center Y) ≃* (Y' ⧸ Subgroup.center Y') := by
  have hle : Subgroup.center Y ≤ (Subgroup.center Y').comap f := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hf g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  refine MulEquiv.ofBijective (QuotientGroup.map _ _ f hle) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : f y ∈ Subgroup.center Y' := (QuotientGroup.eq_one_iff _).1 hx
    exact (QuotientGroup.eq_one_iff _).2 (mem_center_of_map_mem_center f hker h1)
  · intro q
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := hf y'
    exact ⟨QuotientGroup.mk y, rfl⟩

end CentralQuot

section PSimple

variable {G : Type} [Group G]

noncomputable def pSimpleEquivCenterQuot {p : ℕ} (L : Subgroup G) (hcore : GLAPPrimeCore p ↥L = ⊥) :
    PSimple p L ≃* (↥L ⧸ Subgroup.center ↥L) := by
  let e0 : PQuot p L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact QuotientGroup.congr (Subgroup.center (PQuot p L)) (Subgroup.center ↥L) e0
    (Subgroup.map_center_eq e0)

end PSimple

section Lift

variable {K Q : Type} [Group K] [Group Q]

theorem eq_of_map_eq_of_perfect (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    {J₁ J₂ : Subgroup K} (h1 : ⁅J₁, J₁⁆ = J₁) (h2 : ⁅J₂, J₂⁆ = J₂)
    (h : J₁.map π = J₂.map π) : J₁ = J₂ := by
  have key : ∀ {A B : Subgroup K}, ⁅A, A⁆ = A → ⁅B, B⁆ = B → A.map π = B.map π → A ≤ B := by
    intro A B hA hB hAB
    conv_lhs => rw [← hA]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨a', ha', haa⟩ : π a ∈ B.map π := hAB ▸ Subgroup.mem_map_of_mem π ha
    obtain ⟨b', hb', hbb⟩ : π b ∈ B.map π := hAB ▸ Subgroup.mem_map_of_mem π hb
    have hza : a'⁻¹ * a ∈ Subgroup.center K := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, haa, inv_mul_cancel])
    have hzb : b'⁻¹ * b ∈ Subgroup.center K := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbb, inv_mul_cancel])
    have ha_eq : a = a' * (a'⁻¹ * a) := by group
    have hb_eq : b = b' * (b'⁻¹ * b) := by group
    have hcomm : ⁅a, b⁆ = ⁅a', b'⁆ := by
      rw [ha_eq, hb_eq]
      have e : ⁅a' * (a'⁻¹ * a), b' * (b'⁻¹ * b)⁆ = ⁅a', b'⁆ :=
        commutatorElement_mul_mul'
          (Commute.symm (Subgroup.mem_center_iff.1 hza b'))
          (Commute.symm (Subgroup.mem_center_iff.1 hza (b'⁻¹ * b)))
          (Commute.symm (Subgroup.mem_center_iff.1 hzb a'))
      convert e using 2 <;> group
    rw [hcomm]
    exact hB.le (Subgroup.commutator_mem_commutator ha' hb')
  exact le_antisymm (key h1 h2 h) (key h2 h1 h.symm)

end Lift

section Fix

theorem fixSubgroup_conj_eq {G : Type*} [Group G] (g : G) :
    fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set G) := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : g * y * g⁻¹ = y := h
    calc y * g = (g * y * g⁻¹) * g := by rw [h1]
      _ = g * y := by group
  · intro h
    show g * y * g⁻¹ = y
    calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [h]
      _ = y := by group

end Fix

section CoverDich

variable {X : Type} [Group X] [Finite X]

theorem no_glaPComponent_of_pConstrainedShape {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {C : Subgroup Q} (h : PConstrainedShape p C) {J : Subgroup Q}
    (hJ : GLAPComponent p C J) : False := by
  have hlay : GLAPLayer p C = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.glaPLayer_eq_bot_of_constrained
      hp le_rfl (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (constraint_of_pConstrainedShape h)
  have hle : J ≤ GLAPLayer p C := le_sSup hJ
  rw [hlay, le_bot_iff] at hle
  exact glaPComponent_ne_bot' hJ hle

theorem glaPPrimeCoreOf_fixSubgroup_eq_bot {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q]
    (π : K →* Q) (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k)) (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime)
    (hZp : IsPGroup p (Subgroup.center K)) (hO : GLAPPrimeCoreOf p (fixSubgroup β) = ⊥) :
    GLAPPrimeCoreOf p (fixSubgroup α) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := map_glaPPrimeCoreOf_fixSubgroup_le π hker α β hαβ hπ hp
  rw [hO, le_bot_iff] at h1
  set O := GLAPPrimeCoreOf p (fixSubgroup α) with hOdef
  have hle : O ≤ Subgroup.center K := fun x hx => hker (by
    rw [MonoidHom.mem_ker]
    have h2 : π x ∈ O.map π := ⟨x, hx, rfl⟩
    rw [h1] at h2
    exact Subgroup.mem_bot.1 h2)
  have hpg : IsPGroup p ↥O := hZp.of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  have hcop : Nat.Coprime p (Nat.card O) := coprime_card_GLAPPrimeCoreOf hp _
  apply Subgroup.eq_bot_of_card_eq
  rw [hn] at hcop ⊢
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero]
  · exact absurd (Nat.Coprime.eq_one_of_dvd hcop (dvd_pow_self p hpos.ne')) hp.ne_one

theorem glaPPrimeCore_eq_bot_of_subnormal {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {L C : Subgroup G} (hLC : IsSubnormal L C) (hO : GLAPPrimeCoreOf p C = ⊥) :
    GLAPPrimeCore p ↥L = ⊥ := by
  have h : GLAPPrimeCoreOf p L = ⊥ :=
    le_bot_iff.1 ((glaPPrimeCoreOf_le_of_isSubnormal hp hLC).trans hO.le)
  unfold GLAPPrimeCoreOf at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h

noncomputable def pSimpleEquivOfCentralMap {K Q : Type} [Group K] [Group Q] (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) {p : ℕ} {J : Subgroup K} (hJ : ⁅J, J⁆ = J)
    (hcJ : GLAPPrimeCore p ↥J = ⊥) (hcL : GLAPPrimeCore p ↥(J.map π) = ⊥) :
    PSimple p J ≃* PSimple p (J.map π) := by
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJ
  let f : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective π J
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have h1 : (x : K) ∈ π.ker := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 := hker h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (g : K))
  exact (pSimpleEquivCenterQuot J hcJ).trans
    ((quotCenterEquivOfCentral f hf hfker).trans (pSimpleEquivCenterQuot (J.map π) hcL).symm)

theorem comp_dichotomy_cover {p : ℕ} (hp : p.Prime) {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    {K : Subgroup X} (hZp : IsPGroup p (Subgroup.center ↥K))
    (hOall : OPrimeCoreTrivialAt p (↥K ⧸ Subgroup.center ↥K))
    (hshape : CentShape p Good (↥K ⧸ Subgroup.center ↥K))
    {a k : X} (hk : k ∈ K) (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (hkZ : (⟨k, hk⟩ : ↥K) ∉ Subgroup.center ↥K)
    (hkp : (⟨k, hk⟩ : ↥K) ^ p ∈ Subgroup.center ↥K) :
    (∀ J : Subgroup X, ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) ∨
      ∃ J₀ : Subgroup X, J₀ ≤ K ∧
        (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          J = J₀) ∧ Good (PSimple p (J₀.subgroupOf K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k' : ↥K := ⟨k, hk⟩ with hk'
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπdef
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set α : MulAut ↥K := MulAut.conj k' with hα
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.conj (π k') with hβ
  have hαβ : ∀ x, π (α x) = β (π x) := by
    intro x
    simp [hα, hβ, MulAut.conj_apply]
  have hfixα : fixSubgroup α = Subgroup.centralizer ({k'} : Set ↥K) := fixSubgroup_conj_eq k'
  have hfixβ : fixSubgroup β = Subgroup.centralizer ({π k'} : Set (↥K ⧸ Subgroup.center ↥K)) :=
    fixSubgroup_conj_eq (π k')
  have hbar1 : π k' ≠ 1 := fun h => hkZ ((QuotientGroup.eq_one_iff _).1 h)
  have hbarp : (π k') ^ p = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hkp
  have hO : GLAPPrimeCoreOf p (fixSubgroup β) = ⊥ := by
    rw [hfixβ]
    exact hOall (π k') (orderOf_eq_prime hbarp hbar1)
  have hJsub : ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      GLAPComponent p (fixSubgroup α) (J.subgroupOf K) := by
    intro J hJ
    have h1 := glaPComponent_subgroupOf hp
      (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
    rwa [subgroupOf_inf_centralizer_eq hk hc, ← hfixα] at h1
  rcases hshape (π k') hbar1 hbarp with hcon | ⟨L, hL, hu, hG⟩
  · refine Or.inl fun J hJ => ?_
    have h2 := glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp (hJsub J hJ)
    rw [hfixβ] at h2
    exact no_glaPComponent_of_pConstrainedShape hp hcon h2
  · refine Or.inr ?_
    have hL' : GLAPComponent p (fixSubgroup β) L := by rw [hfixβ]; exact hL
    obtain ⟨J₀', hJ₀', hJ₀map⟩ := exists_glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp hL'
    refine ⟨J₀'.map K.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · intro J hJ
      have hJK : J ≤ K := hJ.1.trans inf_le_left
      have h2 := glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp (hJsub J hJ)
      rw [hfixβ] at h2
      have hmapJ : (J.subgroupOf K).map π = L := hu _ h2
      have heq : J.subgroupOf K = J₀' :=
        eq_of_map_eq_of_perfect π hker
          (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect (hJsub J hJ))
          (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ₀')
          (hmapJ.trans hJ₀map.symm)
      rw [← Subgroup.map_subgroupOf_eq_of_le hJK, heq]
    · have h1 : (J₀'.map K.subtype).subgroupOf K = J₀' :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective J₀'
      rw [h1]
      have hcL : GLAPPrimeCore p ↥L = ⊥ :=
        glaPPrimeCore_eq_bot_of_subnormal hp hL'.2.1 hO
      have hOα : GLAPPrimeCoreOf p (fixSubgroup α) = ⊥ :=
        glaPPrimeCoreOf_fixSubgroup_eq_bot π hker α β hαβ hπ hp hZp hO
      have hcJ : GLAPPrimeCore p ↥J₀' = ⊥ :=
        glaPPrimeCore_eq_bot_of_subnormal hp hJ₀'.2.1 hOα
      have hcL' : GLAPPrimeCore p ↥(J₀'.map π) = ⊥ := by rw [hJ₀map]; exact hcL
      have e := pSimpleEquivOfCentralMap π hker
        (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ₀') hcJ hcL'
      rw [hJ₀map] at e
      exact hGood _ _ e.symm hG

end CoverDich

end CFSG.HardMathSupport.Dickson.I271
