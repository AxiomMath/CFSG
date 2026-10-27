module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2KL

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC

section Action

variable {G : Type} [Group G] (A : Subgroup G) [A.Normal]

noncomputable def conjQuot (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : G ⧸ A →* MulAut A :=
  QuotientGroup.lift A (MulAut.conjNormal : G →* MulAut A) (by
    intro g hg
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    show g * (a : G) * g⁻¹ = a
    rw [hA g hg a a.2, mul_inv_cancel_right])

theorem conjQuot_mk (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (g : G) (a : A) :
    ((conjQuot A hA (QuotientGroup.mk g) a : A) : G) = g * a * g⁻¹ := by
  rw [conjQuot, QuotientGroup.lift_mk]
  rfl

theorem conjQuot_injective (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcent : ∀ g : G, (∀ a ∈ A, a * g = g * a) → g ∈ A) :
    Function.Injective (conjQuot A hA) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  rw [QuotientGroup.eq_one_iff]
  apply hcent
  intro a ha
  have h := congrArg (fun m : MulAut A => ((m ⟨a, ha⟩ : A) : G)) hk
  simp only [conjQuot_mk] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem conjQuot_fix_iff (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (S Z : Subgroup G)
    (hZc : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z)
    (hcent : ∀ s ∈ S, s ∉ A → ∀ a ∈ A, a * s = s * a → a ∈ Z) :
    ∀ v ∈ S.map (QuotientGroup.mk' A), v ≠ 1 → ∀ a : A,
      conjQuot A hA v a = a ↔ a ∈ Z.subgroupOf A := by
  intro v hv hv1 a
  obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.1 hv
  have hsA : s ∉ A := fun h => hv1 ((QuotientGroup.eq_one_iff s).2 h)
  rw [Subgroup.mem_subgroupOf, ← Subtype.coe_inj]
  change ((conjQuot A hA (QuotientGroup.mk s) a : A) : G) = a ↔ _
  rw [conjQuot_mk]
  constructor
  · intro h
    exact hcent s hsS hsA a a.2 (mul_inv_eq_iff_eq_mul.1 h).symm
  · intro h
    exact mul_inv_eq_iff_eq_mul.2 (hZc a h s hsS).symm

theorem conjQuot_not_forall (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (Z : Subgroup G)
    (hZA : Z ≤ A) (hZn : ¬ Z.Normal) :
    ¬ (∀ k : G ⧸ A, ∀ a ∈ Z.subgroupOf A, conjQuot A hA k a ∈ Z.subgroupOf A) := by
  intro h
  apply hZn
  refine ⟨fun z hz g => ?_⟩
  have := h (QuotientGroup.mk g) ⟨z, hZA hz⟩ (by simpa [Subgroup.mem_subgroupOf] using hz)
  rw [Subgroup.mem_subgroupOf, conjQuot_mk] at this
  exact this

end Action

end CFSG.OddStandard.ThmC.O2

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC

variable {G : Type} [Group G] [Finite G]

theorem centralizer_A_le (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) [td.A.Normal] :
    ∀ g : G, (∀ a ∈ td.A, a * g = g * a) → g ∈ td.A := by
  intro g hg
  have hAp : IsPGroup 2 td.A := IsPGroup.of_card (p := 2) (n := 4) (by rw [td.card_A]; norm_num)
  have hAR : td.A ≤ centralizer (td.A : Set G) := fun x hx y hy => td.A_abel y hy x hx
  have hnotZ : ∃ a ∈ td.A, a ∉ td.Z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show td.A ≤ td.Z from hcon)
    rw [td.card_A, td.card_Z] at this
    omega
  obtain ⟨a, ha, haZ⟩ := hnotZ
  have hSR : (S : Subgroup G) ⊓ centralizer (td.A : Set G) = td.A := by
    refine le_antisymm (fun x hx => ?_) (le_inf td.A_le_S hAR)
    exact td.cent_A a ha haZ x hx.1 (hx.2 a ha).symm
  have hodd : ¬ 2 ∣ td.A.relIndex (centralizer (td.A : Set G)) := by
    have := sylow_inf_normal_relIndex_odd S (centralizer (td.A : Set G))
    rwa [hSR] at this
  have hRA : centralizer (td.A : Set G) = td.A :=
    eq_of_central_sylow hO _ td.A hAR hAp hodd (fun x hx p hp => (hx p hp).symm)
  exact hRA.le (mem_centralizer_iff.2 hg)

omit [Finite G] in
theorem pCore_quot_eq_bot (A : Subgroup G) [A.Normal] (hA : IsPGroup 2 A)
    (hD : pCore 2 G = A) : pCore 2 (G ⧸ A) = ⊥ := by
  have hQn : ((pCore 2 (G ⧸ A)).comap (QuotientGroup.mk' A)).Normal := pCore_normal.comap _
  have hQp : IsPGroup 2 ((pCore 2 (G ⧸ A)).comap (QuotientGroup.mk' A)) := by
    refine (pCore_isPGroup (p := 2) (G := G ⧸ A)).comap_of_ker_isPGroup (QuotientGroup.mk' A) ?_
    rwa [QuotientGroup.ker_mk']
  have hle : (pCore 2 (G ⧸ A)).comap (QuotientGroup.mk' A) ≤ pCore 2 G := le_sSup ⟨hQn, hQp⟩
  rw [hD] at hle
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact (QuotientGroup.eq_one_iff g).2 (hle hx)

omit [Finite G] in
theorem card_map_mkA (A S : Subgroup G) [A.Normal] (hAS : A ≤ S) (hA : Nat.card A = 16)
    (hS : Nat.card S = 64) : Nat.card (S.map (QuotientGroup.mk' A)) = 4 := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have h := Subgroup.relIndex_mul_card A S
  rw [inf_of_le_left hAS, hA, hS] at h
  omega

end CFSG.OddStandard.ThmC.O2

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC

variable {G : Type} [Group G] [Finite G]

theorem caseII_conseq (hA8 : A8Fact) (hGor : Gor42) (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) (hD : pCore 2 G = td.A) (hSn : ¬ (S : Subgroup G).Normal)
    [td.A.Normal] :
    (Nonempty (G ⧸ td.A ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (G ⧸ td.A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) ∧
    ∀ u v : td.A, u ≠ 1 → v ≠ 1 → ∃ g : G, g * u * g⁻¹ = v := by
  have hAp : IsPGroup 2 td.A := IsPGroup.of_card (p := 2) (n := 4) (by rw [td.card_A]; norm_num)
  have hZn : ¬ td.Z.Normal := fun hZ => hSn (kl hGor hO S td hZ)
  have hρ := conjQuot_injective td.A td.A_abel (centralizer_A_le hO S td)
  have hVcard : Nat.card ((S.mapSurjective (QuotientGroup.mk'_surjective td.A) :
      Sylow 2 (G ⧸ td.A)) : Subgroup (G ⧸ td.A)) = 4 :=
    card_map_mkA td.A S td.A_le_S td.card_A td.card_S
  have hVsq : ∀ v ∈ ((S.mapSurjective (QuotientGroup.mk'_surjective td.A) :
      Sylow 2 (G ⧸ td.A)) : Subgroup (G ⧸ td.A)), v * v = 1 := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hv
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (s * s)).2 (td.Z_le_A (td.sq_mem_Z s hs))
  have hZcard : Nat.card (td.Z.subgroupOf td.A) = 4 := by
    rw [← td.card_Z]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe td.Z_le_A).toEquiv
  have hfix := conjQuot_fix_iff td.A td.A_abel S td.Z
    (fun z hz s hs => (((td.mem_Z z).1 hz).2 s hs)) td.cent_not_A
  obtain ⟨hiso, htrans⟩ := hA8 (G ⧸ td.A) td.A (fun a b => Subtype.ext (td.A_abel a a.2 b b.2))
    (fun a => Subtype.ext (td.A_sq a a.2)) td.card_A (conjQuot td.A td.A_abel) hρ
    (pCore_quot_eq_bot td.A hAp hD) (S.mapSurjective (QuotientGroup.mk'_surjective td.A)) hVcard
    hVsq (td.Z.subgroupOf td.A) hZcard hfix (conjQuot_not_forall td.A td.A_abel td.Z td.Z_le_A hZn)
  refine ⟨hiso, fun u v hu hv => ?_⟩
  obtain ⟨k, hk⟩ := htrans u v hu hv
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  exact ⟨g, by simpa [conjQuot_mk] using congrArg Subtype.val hk⟩

end CFSG.OddStandard.ThmC.O2

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC

variable {G : Type} [Group G] [Finite G]

theorem caseII (hA8 : A8Fact) (hGor : Gor42) (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) (hD : pCore 2 G = td.A) (hSn : ¬ (S : Subgroup G).Normal) :
    Concl G S := by
  have hAn : td.A.Normal := by rw [← hD]; exact pCore_normal
  obtain ⟨hiso, htrans⟩ := caseII_conseq hA8 hGor hO S td hD hSn
  have hcent := centralizer_A_le hO S td
  unfold Concl
  refine ⟨?_, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hD]
    exact fun g hg => hcent g (mem_centralizer_iff.1 hg)
  · rw [hD]
    exact td.A_le_S
  · rw [hD]
    exact td.card_A
  · intro b hb
    rw [hD] at hb
    exact td.A_sq b hb
  · intro b hb c hc
    rw [hD] at hb hc
    exact td.A_abel b hb c hc
  · exact hiso.imp (fun ⟨i⟩ => ⟨(QuotientGroup.quotientMulEquivOfEq hD).trans i⟩)
      (fun ⟨i⟩ => ⟨(QuotientGroup.quotientMulEquivOfEq hD).trans i⟩)
  · intro u hu v hv hu1 hv1
    rw [hD] at hu hv
    obtain ⟨g, hg⟩ := htrans ⟨u, hu⟩ ⟨v, hv⟩ (fun h => hu1 (congrArg Subtype.val h))
      (fun h => hv1 (congrArg Subtype.val h))
    exact ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

end CFSG.OddStandard.ThmC.O2
