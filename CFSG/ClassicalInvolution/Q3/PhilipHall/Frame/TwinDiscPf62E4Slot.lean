module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf60SlotGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf58Shapes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc

namespace ExitE4

@[expose] def E4Sp6SqModel : Prop :=
  ∀ (M : Type) [Group M] [Finite M], CFSG.Blueprint.LieModel M .PSp 3 2 1 →
    ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
      (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
        ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
      ∀ K' ∈ CoreAssembly.conjClass K, K' ≠ K → K' ≤ Subgroup.normalizer (K : Set M) →
        ∀ β : MulAut M, (∀ k ∈ K, β k = k) → (∀ k ∈ K', β k = k) → β * β = 1

@[expose] def E4O8TwinModel : Prop :=
  ∀ (M : Type) [Group M] [Finite M], CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1 →
    ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
      (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
        ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
      ∃ J₁ J₂ : Subgroup M, J₁ ∈ CoreAssembly.conjClass K ∧ J₂ ∈ CoreAssembly.conjClass K ∧
        J₁ ≠ K ∧ J₂ ≠ K ∧ J₁ ≠ J₂ ∧ J₁ ≤ Subgroup.normalizer (K : Set M) ∧
        J₂ ≤ Subgroup.normalizer (K : Set M)

section Quot

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem center_eq_bot_of_quat {M : Type} [Group M] [IsSimpleGroup M] {K : Subgroup M}
    (hq : Nonempty (↥K ≃* QuaternionGroup 2)) : Subgroup.center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
  · exact h
  · exfalso
    obtain ⟨e⟩ := hq
    have hc := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top
      ((e.symm (QuaternionGroup.a 1) : ↥K) : M)) ((e.symm (QuaternionGroup.xa 0) : ↥K) : M)
    have h1 : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) =
        e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) := Subtype.ext hc
    rw [← map_mul, ← map_mul] at h1
    exact absurd (e.symm.injective h1) (by decide)

theorem twinDatum_quot (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J)
    (hq8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2)) {N : Subgroup X} [N.Normal]
    (hNc : N ≤ Subgroup.center X) (hmeet : ∀ J ∈ Φ, J ⊓ N = ⊥) {K : Subgroup X} (hK : K ∈ Φ)
    {z : X} (hz : IsUniqueInvolution K z) :
    Nonempty (↥(K.map (QuotientGroup.mk' N)) ≃* QuaternionGroup 2) ∧
      IsUniqueInvolution (K.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N z) ∧
      ∀ c ∈ Subgroup.centralizer ({QuotientGroup.mk' N z} : Set (X ⧸ N)),
        conjSub c (K.map (QuotientGroup.mk' N)) = K.map (QuotientGroup.mk' N) ∨
          ∀ x ∈ K.map (QuotientGroup.mk' N), ∀ y ∈ conjSub c (K.map (QuotientGroup.mk' N)),
            x * y = y * x := by
  have hnab := exists_noncomm hΩ h2 hK
  refine ⟨?_, AscQuot.isUniqueInvolution_map_mk (hmeet K hK) hz, ?_⟩
  · obtain ⟨eK⟩ := hq8 K hK
    exact ⟨(AscQuot.quotRestrictEquiv (hmeet K hK)).symm.trans eK⟩
  · intro cb hcb
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N cb
    have hc' : QuotientGroup.mk' N c * QuotientGroup.mk' N z =
        QuotientGroup.mk' N z * QuotientGroup.mk' N c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hq : z⁻¹ * (c * z * c⁻¹) ∈ N := by
      have h0 : QuotientGroup.mk' N (z⁻¹ * (c * z * c⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc', mul_inv_cancel_right, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have hcen : ∀ y : X, y * (z⁻¹ * (c * z * c⁻¹)) = (z⁻¹ * (c * z * c⁻¹)) * y :=
      Subgroup.mem_center_iff.mp (hNc hq)
    rcases twin_clause_central hΩ h2 hK hz hnab rfl hcen with h | h
    · left
      rw [← AscQuot.map_conjSub, h]
    · right
      rintro _ ⟨x, hx, rfl⟩ y hy
      rw [← AscQuot.map_conjSub] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, h x hx y' hy']

theorem exists_induced_aut {N : Subgroup X} [N.Normal] (hNc : N ≤ Subgroup.center X)
    (hZ : Subgroup.center (X ⧸ N) = ⊥) (α : MulAut X) :
    ∃ β : MulAut (X ⧸ N), ∀ x : X, β (QuotientGroup.mk x) = QuotientGroup.mk (α x) := by
  have hle : N.map α.toMonoidHom ≤ N := by
    rintro _ ⟨n, hn, rfl⟩
    have hcen : α n ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.mp (hNc hn) (α.symm g)
      calc g * α n = α (α.symm g * n) := by simp
        _ = α (n * α.symm g) := by rw [h1]
        _ = α n * g := by simp
    have hc2 : (QuotientGroup.mk (α n) : X ⧸ N) ∈ Subgroup.center (X ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro g'
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hcen g]
    rw [hZ, Subgroup.mem_bot] at hc2
    exact (QuotientGroup.eq_one_iff _).mp hc2
  have heq : N.map α.toMonoidHom = N :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective α.injective])
  exact ⟨QuotientGroup.congr N N α heq, fun x => QuotientGroup.congr_mk N N α heq x⟩

theorem sqTriOn_of_twinE4 (hSp : E4Sp6SqModel) (hO8 : E4O8TwinModel) (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J)
    (hno : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → ¬ TightInO2 z) (hTO : TwinOnlyNbr Φ)
    (hE : TwinE4 X) : SqTriOn X Φ := by
  intro A B x₀ hA hB hxA hxB α hα4 hperm hfixA hfixB
  left
  have hΩ := hS.hyp
  have hgen := hS.gen
  have hq8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2) := fun J hJ =>
    hS.q8 J hJ J (Vtx.isSylow2In_self (h2 J hJ))
  obtain ⟨Q, hQ, f, hfs, hker2, hM⟩ := hE
  have hzN : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → u ∉ f.ker := fun J hJ u hu huN =>
    hno J hJ u hu ⟨f.ker, inferInstance, hker2, huN⟩
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => inf_eq_bot h2 hΩ hzN hJ
  have hNc : f.ker ≤ Subgroup.center X := center_of_meet hΩ h2 hgen hker2 hmeet
  have hc : CentQuotGen Φ f.ker := centQuotGen hΩ h2 hNc hmeet
  let e : (X ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : ExLie (X ⧸ f.ker) :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  obtain ⟨hq8A, hinvA, htwA⟩ := twinDatum_quot hΩ h2 hq8 hNc hmeet hA hxA
  have hΦ : Φ = CoreAssembly.conjClass A := by
    ext J
    constructor
    · intro hJ
      exact htrans A hA J hJ
    · rintro ⟨g, rfl⟩
      exact hΩ.conjInvariant g A hA
  have hnbr : ∀ J, J ∈ omegaNbr Φ A ↔
      J ∈ Φ ∧ J ≠ A ∧ J ≤ Subgroup.normalizer (A : Set X) := by
    intro J
    have := Vtx.mem_omegaNbr_conjClass_iff (K₀ := A) (K := A) (J := J) (h2 A hA)
    rw [← hΦ] at this
    exact this
  have hmapC : ∀ y : X, (conjSub y A).map (QuotientGroup.mk' f.ker) =
      conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) :=
    fun y => AscQuot.map_conjSub _ _ _
  rcases hMq with hSpM | hO8M
  ·
    have : IsSimpleGroup (X ⧸ f.ker) := Vtx.isSimpleGroup_of_exLie (Or.inl hSpM)
    have hZ : Subgroup.center (X ⧸ f.ker) = ⊥ := center_eq_bot_of_quat hq8A
    obtain ⟨β, hβ⟩ := exists_induced_aut hNc hZ α
    obtain ⟨hBΦ, hBA, hBN⟩ := (hnbr B).mp hB
    have hBconj : B.map (QuotientGroup.mk' f.ker) ∈
        CoreAssembly.conjClass (A.map (QuotientGroup.mk' f.ker)) := by
      obtain ⟨g, rfl⟩ := htrans A hA B hBΦ
      exact ⟨QuotientGroup.mk' f.ker g, (hmapC g).symm⟩
    have hBne : B.map (QuotientGroup.mk' f.ker) ≠ A.map (QuotientGroup.mk' f.ker) :=
      fun h => hBA (hc.eq_of_map B hBΦ A hA h)
    have hBle : B.map (QuotientGroup.mk' f.ker) ≤
        Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) := by
      rintro _ ⟨b, hb, rfl⟩
      rw [mem_normalizer_iff_conjSub_eq, ← hmapC b, mem_normalizer_iff_conjSub_eq.mp (hBN hb)]
    have hfix : ∀ {L : Subgroup X}, (∀ a ∈ L, α a = a) →
        ∀ k ∈ L.map (QuotientGroup.mk' f.ker), β k = k := by
      rintro L hL _ ⟨a, ha, rfl⟩
      have := hβ a
      rw [hL a ha] at this
      exact this
    have hsq := hSp (X ⧸ f.ker) hSpM (A.map (QuotientGroup.mk' f.ker))
      (QuotientGroup.mk' f.ker x₀) hq8A hinvA htwA _ hBconj hBne hBle β (hfix hfixA) (hfix hfixB)
    have hζf : ∀ x : X, QuotientGroup.mk' f.ker ((α * α) x) = QuotientGroup.mk' f.ker x := by
      intro x
      have h1 : β (β (QuotientGroup.mk' f.ker x)) = QuotientGroup.mk' f.ker x := by
        have := congrArg (fun γ : MulAut (X ⧸ f.ker) => γ (QuotientGroup.mk' f.ker x)) hsq
        simpa using this
      have h2' : β (QuotientGroup.mk' f.ker x) = QuotientGroup.mk' f.ker (α x) := hβ x
      have h3 : β (QuotientGroup.mk' f.ker (α x)) = QuotientGroup.mk' f.ker (α (α x)) := hβ (α x)
      rw [MulAut.mul_apply, ← h3, ← h2', h1]
    have hperm2 : ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map (α * α).toMonoidHom = L' := by
      intro L hL
      obtain ⟨L₁, hL₁, hL₁e⟩ := hperm L hL
      obtain ⟨L₂, hL₂, hL₂e⟩ := hperm L₁ hL₁
      refine ⟨L₂, hL₂, ?_⟩
      rw [← hL₂e, ← hL₁e, Subgroup.map_map]
      rfl
    refine mulAut_eq_one_of_trivial_mod hgen (QuotientGroup.mk' f.ker) (α * α) hperm2 hζf
      (fun K hK K' hK' h => hc.eq_of_map K hK K' hK' h) (fun K hK m hm hm1 => ?_)
    have hmem : m ∈ K ⊓ f.ker := ⟨hm, (QuotientGroup.eq_one_iff m).mp hm1⟩
    rw [hmeet K hK, Subgroup.mem_bot] at hmem
    exact hmem
  ·
    exfalso
    obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ₁A, hJ₂A, hJ₁₂, hn₁, hn₂⟩ :=
      hO8 (X ⧸ f.ker) hO8M (A.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker x₀) hq8A
        hinvA htwA
    have lift : ∀ J ∈ CoreAssembly.conjClass (A.map (QuotientGroup.mk' f.ker)),
        J ≠ A.map (QuotientGroup.mk' f.ker) →
        J ≤ Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) →
          ∃ B' ∈ omegaNbr Φ A, B'.map (QuotientGroup.mk' f.ker) = J := by
      rintro J ⟨h, rfl⟩ hne hle
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h
      have hne' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≠
          A.map (QuotientGroup.mk' f.ker) := hne
      have hle' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≤
          Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) := hle
      refine ⟨conjSub y A, (hnbr _).mpr ⟨hΩ.conjInvariant y A hA, ?_, ?_⟩, hmapC y⟩
      · intro hyA
        apply hne'
        rw [← hmapC, hyA]
      · intro b hb
        refine hc.normalizer_of_map A hA b (hle' ?_)
        rw [← hmapC]
        exact Subgroup.mem_map_of_mem _ hb
    obtain ⟨B₁, hB₁, hB₁J⟩ := lift J₁ hJ₁ hJ₁A hn₁
    obtain ⟨B₂, hB₂, hB₂J⟩ := lift J₂ hJ₂ hJ₂A hn₂
    exact hJ₁₂ (by rw [← hB₁J, ← hB₂J, hTO A hA B₁ hB₁ B₂ hB₂])

end Quot

end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
