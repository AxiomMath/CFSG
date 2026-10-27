module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSchur
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open CFSG Subgroup CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne
open scoped commutatorElement MatrixGroups

variable {G L : Type} [Group G] [Group L]

theorem exists_central_lift [Group.IsPerfect G] (α : G →* L) (hker : α.ker ≤ center G)
    {T : Subgroup G} {Q : Subgroup L} (hTQ : T.map α = Q) (hinj : ∀ z ∈ T, α z = 1 → z = 1)
    {c : L} (hcZ : c ∈ center L) (hcQ : c ∈ Q) (hc2 : orderOf c = 2) :
    ∃ x₀ ∈ T, α x₀ = c ∧ x₀ ∈ center G ∧ orderOf x₀ = 2 := by
  rw [← hTQ] at hcQ
  obtain ⟨x₀, hx₀, rfl⟩ := hcQ
  refine ⟨x₀, hx₀, rfl, ?_, ?_⟩
  · have hz : ∀ a : G, ∃ z ∈ center G, x₀ * a * x₀⁻¹ = a * z := by
      intro a
      refine ⟨a⁻¹ * (x₀ * a * x₀⁻¹), hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv,
        ← (mem_center_iff.1 hcZ (α a)), mul_inv_cancel_right, inv_mul_cancel]
    have hcomm : ∀ a b : G, x₀ * ⁅a, b⁆ * x₀⁻¹ = ⁅a, b⁆ := by
      intro a b
      obtain ⟨za, hza, ha⟩ := hz a
      obtain ⟨zb, hzb, hb⟩ := hz b
      have e : x₀ * ⁅a, b⁆ * x₀⁻¹ = ⁅x₀ * a * x₀⁻¹, x₀ * b * x₀⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, ha, hb, commutatorElement_mul_mul_center hza hzb]
    have hle : commutator G ≤ centralizer ({x₀} : Set G) := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [mem_centralizer_singleton_iff]
      calc ⁅a, b⁆ * x₀ = x₀ * ⁅a, b⁆ * x₀⁻¹ * x₀ := by rw [hcomm a b]
        _ = x₀ * ⁅a, b⁆ := by group
    have htop := Group.isPerfect_def.1 ‹Group.IsPerfect G›
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({x₀} : Set G) := hle (htop ▸ mem_top g)
    rw [mem_centralizer_singleton_iff] at hg
    exact hg
  · have hc1 : α x₀ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hc2
      exact absurd hc2 (by norm_num)
    refine orderOf_eq_prime ?_ fun h => hc1 (by rw [h, map_one])
    apply hinj _ (pow_mem hx₀ 2)
    rw [map_pow, ← hc2, pow_orderOf_eq_one]

variable [Finite G] [Finite L]

theorem propBHypII_lift [Group.IsPerfect G]
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* G),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ σ : G →* E, ∀ x, π (σ x) = x)
    (α : G →* L) (hα : Function.Surjective α) (hker : α.ker ≤ center G)
    (hker2 : IsPGroup 2 α.ker) {s : MulAut L} (hs2 : orderOf s = 2) {Q : Subgroup L}
    (hQs : Q ≤ autFixed s) (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s)))
    {p₁ n₁ : ℕ} [Fact p₁.Prime] (hp₁ : p₁ ≠ 2) (hn₁ : 0 < n₁)
    (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, GaloisField p₁ n₁))
    {x₀ : G} (hx₀ : x₀ ∈ ⁅Q.comap α, Q.comap α⁆) (hx₀Z : x₀ ∈ center G)
    (hx₀2 : orderOf x₀ = 2) : PropBHypII G x₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF₁ : ringChar (GaloisField p₁ n₁) ≠ 2 := by
    rw [ringChar.eq (GaloisField p₁ n₁) p₁]
    exact hp₁
  have hQQ : ⁅Q, Q⁆ = Q := C.commutator_eq_of_isPComponent hQs hQc
  obtain ⟨hTQ, -, hinj⟩ := perfectLift_spec α hα hker hker2 hQQ hF₁ e
  set T := ⁅Q.comap α, Q.comap α⁆ with hT
  obtain ⟨s₀, hs₀, hs₀s, -⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit
    (β := (s : L →* L).comp α) (η := α) (s.surjective.comp hα) hα hker hker2
  have hs₀i : Function.Injective s₀ := Finite.injective_iff_surjective.2 hs₀s
  set s' : MulAut G := MulEquiv.ofBijective s₀ ⟨hs₀i, hs₀s⟩ with hs'
  have hs'α : ∀ x, α (s' x) = s (α x) := fun x => hs₀ x
  have hs'2 : s' * s' = 1 := by
    have h := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
      (θ := α) hker (s' * s').toMonoidHom (MonoidHom.id G) fun x => by
        change α (s' (s' x)) = α x
        rw [hs'α, hs'α]
        have hss : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
        exact DFunLike.congr_fun hss (α x)
    exact MulEquiv.ext fun x => DFunLike.congr_fun h x
  have hs'1 : s' ≠ 1 := by
    intro h
    have hs1 : s = 1 := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := hα y
      rw [← hs'α, h]
      rfl
    rw [hs1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have hs'o : orderOf s' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs'2) hs'1
  have hTfix : T ≤ autFixed s' := by
    have hlift : ∀ y ∈ Q.comap α, ∃ z ∈ center G, s' y = y * z := by
      intro y hy
      refine ⟨y⁻¹ * s' y, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs'α, show s (α y) = α y from hQs hy,
        inv_mul_cancel]
    rw [hT, commutator_le]
    intro a ha b hb
    obtain ⟨za, hza, hsa⟩ := hlift a ha
    obtain ⟨zb, hzb, hsb⟩ := hlift b hb
    rw [mem_autFixed_iff, map_commutatorElement, hsa, hsb,
      commutatorElement_mul_mul_center hza hzb]
  set D := (autFixed s).comap α with hD
  have hsD : autFixed s' ≤ D := autFixed_le_comap α hs'α
  have hTD : T ≤ D := hTfix.trans hsD
  set q : D →* autFixed s := (α.comp D.subtype).codRestrict (autFixed s) fun d => d.2 with hqdef
  have hq : Function.Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hα y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hkerq : ∀ d : D, q d = 1 ↔ α d = 1 := fun d =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcen : q.ker ≤ center D := by
    intro d hd
    have h1 : (d : G) ∈ center G := hker ((hkerq d).mp hd)
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp h1 g)
  have h2q : IsPGroup 2 q.ker := by
    intro d
    obtain ⟨k, hk⟩ := hker2 ⟨((d : D) : G), (hkerq d).mp d.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : α.ker => (y : G)) hk
    simpa using this
  have hQ' := (CatalogueBAlternating.pComponent_two_iff _).mp hQc
  obtain ⟨Q₁, hQ₁, hQ₁m⟩ := CentralTwoKernelComponents.exists_lift q hq hcen h2q _ hQ'
  have hQ₁e := CentralTwoKernelComponents.derived_preimage_eq q hcen Q₁ hQ₁
  rw [hQ₁m] at hQ₁e
  have hcomap : ((Q.subgroupOf (autFixed s)).comap q).map D.subtype = Q.comap α := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hd
    · intro hx
      exact ⟨⟨x, hQs hx⟩, hx, rfl⟩
  have hQ₁T : Q₁.map D.subtype = T := by
    rw [← hQ₁e, Subgroup.map_commutator, hcomap]
  have hQ₁eq : Q₁ = T.subgroupOf D :=
    Subgroup.map_injective D.subtype_injective (by rw [hQ₁T, map_subgroupOf_eq_of_le hTD])
  rw [hQ₁eq] at hQ₁
  have hTc : TwoComponents.IsTwoComponent (T.subgroupOf (autFixed s')) :=
    TwoComponentTransport.restrict_nested T (autFixed s') D hTfix hsD hQ₁
  have hTQm : ∀ z ∈ T, α z ∈ Q := fun z hz =>
    (Subgroup.commutator_le_self (Q.comap α) hz : z ∈ Q.comap α)
  set αT : T →* Q := (α.comp T.subtype).codRestrict Q fun z => hTQm z z.2 with hαT
  have hαTinj : Function.Injective αT := by
    intro a b hab
    have h' : α (a : G) = α (b : G) := congrArg Subtype.val hab
    apply Subtype.ext
    have := hinj ((a : G) * (b : G)⁻¹) (mul_mem a.2 (inv_mem b.2))
      (by rw [map_mul, map_inv, h', mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  have hαTsurj : Function.Surjective αT := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ T.map α := by rw [hTQ]; exact hy
    obtain ⟨z, hz, rfl⟩ := hy'
    exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨s', hs'o, T, hTfix, (CatalogueBAlternating.pComponent_two_iff _).mpr hTc,
    ⟨p₁, n₁, inferInstance, hp₁, hn₁,
      ⟨(C.quotientPPrimeCoreEquiv (MulEquiv.ofBijective αT ⟨hαTinj, hαTsurj⟩)).trans e⟩⟩,
    hx₀Z, hx₀, hx₀2⟩

end CFSG.ComponentClassification.Burgoyne.DX.Dr
