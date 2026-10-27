module

public import CFSG.CGT.Foote81L6.MainRank
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallSDClose
public import CFSG.Holt.TwoGroups
public import CFSG.CGT.Foote81L6.Star
public import CFSG.ClassicalInvolution.NormalQuaternion

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

section Lift

variable {H : Type} [Group H]

theorem mem_comm_of_center_eq {S : Subgroup H} {z : H}
    (hZ : (center ↥S).map S.subtype = zpowers z) : z ∈ S ∧ ∀ s ∈ S, s * z = z * s := by
  have hz : z ∈ (center ↥S).map S.subtype := hZ ▸ mem_zpowers z
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨y.2, fun s hs => ?_⟩
  have := mem_center_iff.1 hy ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem le_centralizer_of_center_eq {S : Subgroup H} {z : H}
    (hZ : (center ↥S).map S.subtype = zpowers z) : S ≤ centralizer ({z} : Set H) :=
  fun s hs => mem_centralizer_singleton_iff.2 ((mem_comm_of_center_eq hZ).2 s hs)

variable [Finite H]

theorem sylowQuot_isPGroup_and_max (S : Sylow 2 H) {z : H}
    (hSz : (S : Subgroup H) ≤ centralizer ({z} : Set H)) :
    IsPGroup 2 (sylowQuot S z) ∧ ∀ {Q : Subgroup (centralizerQuot z)}, IsPGroup 2 Q →
      sylowQuot S z ≤ Q → Q = sylowQuot S z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Sylow 2 (centralizerQuot z) :=
    (S.subtype hSz).mapSurjective (QuotientGroup.mk'_surjective (zpowers (zCent z)))
  have hEq : (S' : Subgroup (centralizerQuot z)) = sylowQuot S z := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
    rfl
  refine ⟨hEq ▸ S'.isPGroup', fun {Q} hQ hle => ?_⟩
  rw [← hEq] at hle ⊢
  exact S'.is_maximal' hQ hle

@[expose] noncomputable def sylowQuotSylow (S : Sylow 2 H) {z : H}
    (hSz : (S : Subgroup H) ≤ centralizer ({z} : Set H)) : Sylow 2 (centralizerQuot z) :=
  Sylow.mk (sylowQuot S z) (sylowQuot_isPGroup_and_max S hSz).1 (by
    intro Q hQ hle
    exact (sylowQuot_isPGroup_and_max S hSz).2 hQ hle)

end Lift

section Main

variable {H : Type} [Group H] [Finite H]

theorem normalQuaternionAt_of_closed (S : Sylow 2 H) {z : H}
    (hZ : (center ↥(S : Subgroup H)).map (S : Subgroup H).subtype = zpowers z)
    (hz2 : orderOf z = 2) {m n : ℕ} (D₀ : FooteCore (centralizerQuot z) (sylowQuot S z) m n)
    (hcl : StronglyInvolutionClosed D₀.A (sylowQuot S z))
    (hlift : ∀ g : centralizer ({z} : Set H), (g : H) ∈ (S : Subgroup H) →
      (QuotientGroup.mk g : centralizerQuot z) ∈ D₀.A →
      orderOf (QuotientGroup.mk g : centralizerQuot z) = 2 → (g : H) ^ 2 = z) :
    CFSG.ClassicalInvolution.NormalQuaternionAt z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set H)
  set Zc : Subgroup C := zpowers (zCent z)
  set π : C →* centralizerQuot z := QuotientGroup.mk' Zc
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Zc
  have hSz := le_centralizer_of_center_eq hZ
  have hzS := (mem_comm_of_center_eq hZ).1
  set T := sylowQuotSylow S hSz
  have hT : (T : Subgroup (centralizerQuot z)) = sylowQuot S z := rfl
  set A₀ := D₀.A
  set K := normalClosure (A₀ : Set (centralizerQuot z))
  have hTmax : ∀ Q : Subgroup (centralizerQuot z), IsPGroup 2 Q → sylowQuot S z ≤ Q →
      Q = sylowQuot S z := fun Q hQ hle => T.is_maximal' hQ hle
  have hhyp := D₀.goldschmidt_hyp hTmax hcl
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 ((sylowQuot S z) ⊓ K) K := by
    have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (sylowQuot S z) ⊤ := by
      refine ⟨T.subtype le_top, ?_⟩
      rw [Sylow.coe_subtype, subgroupOf_map_subtype, hT, inf_top_eq]
    exact h1.inf_of_le_normalizer le_top (by rw [normalizer_eq_top])
  have hrank := CFSG.ComponentClassification.Foote5.HallGen.goldschmidtCorB4 (centralizerQuot z)
    A₀ ⟨m, D₀.two_le_m, D₀.A_iso⟩ hhyp _ hTK
  have hAK : A₀ ≤ K := subset_normalClosure
  have hP : (sylowQuot S z) ⊓ K = A₀ := by
    refine D₀.eq_A_of_card_le_four inf_le_left (le_inf D₀.A_le_T hAK) ?_ hrank
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    rw [mem_inf, mem_inf]
    have h1 := mem_normalizer_iff.1 (le_normalizer hg) x
    have h2 : x ∈ K ↔ g * x * g⁻¹ ∈ K := ⟨fun hx => (normalClosure_normal).conj_mem x hx g,
      fun hx => by
        have := (normalClosure_normal (s := (A₀ : Set (centralizerQuot z)))).conj_mem _ hx g⁻¹
        simpa [mul_assoc] using this⟩
    rw [h1, h2]
  obtain ⟨AK, hAKeq⟩ := hTK
  rw [hP] at hAKeq
  set Kc : Subgroup C := K.comap π
  have hKcN : Kc.Normal := Subgroup.Normal.comap normalClosure_normal π
  set φ : ↥Kc →* ↥K := (π.comp Kc.subtype).codRestrict K (fun x => x.2)
  have hφ : ∀ x : ↥Kc, ((φ x : centralizerQuot z)) = π x := fun x => rfl
  have hφsurj : Function.Surjective φ := by
    intro k
    obtain ⟨c, hc⟩ := hπ (k : centralizerQuot z)
    have hcK : c ∈ Kc := by
      show π c ∈ K
      rw [hc]
      exact k.2
    exact ⟨⟨c, hcK⟩, Subtype.ext hc⟩
  have hπz : π (zCent z) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_zpowers _
  have hzK : zCent z ∈ Kc := by
    show π (zCent z) ∈ K
    rw [hπz]
    exact one_mem _
  have hzz : zCent z * zCent z = 1 := by
    apply Subtype.ext
    show z * z = 1
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hker : IsPGroup 2 φ.ker := by
    intro x
    refine ⟨1, ?_⟩
    have hxZ : ((x : ↥Kc) : C) ∈ Zc := by
      have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have := congrArg Subtype.val hx
      rw [hφ] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 := mul_self_eq_one_of_mem_zpowers hzz hxZ
    rw [pow_one, sq]
    exact Subtype.ext (Subtype.ext (by simpa using h2))
  have hrange : (AK : Subgroup ↥K) ≤ φ.range := by
    rw [MonoidHom.range_eq_top.2 hφsurj]
    exact le_top
  set QK : Sylow 2 ↥Kc := AK.comapOfKerIsPGroup φ hker hrange
  have hmemAK : ∀ k : ↥K, k ∈ (AK : Subgroup ↥K) ↔ (k : centralizerQuot z) ∈ A₀ := by
    intro k
    constructor
    · intro hk
      rw [← hAKeq]
      exact ⟨k, hk, rfl⟩
    · intro hk
      rw [← hAKeq] at hk
      obtain ⟨k', hk', hkk'⟩ := hk
      have : k' = k := Subtype.ext hkk'
      rwa [← this]
  have hmemQK : ∀ y : ↥Kc, y ∈ (QK : Subgroup ↥Kc) ↔ π y ∈ A₀ := by
    intro y
    rw [Sylow.coe_comapOfKerIsPGroup, mem_comap, hmemAK, hφ]
  have hS : ∀ y : C, π y ∈ A₀ → (y : H) ∈ (S : Subgroup H) := by
    intro y hy
    have hyT : π y ∈ sylowQuot S z := D₀.A_le_T hy
    obtain ⟨s, hs, hsy⟩ := hyT
    replace hs : (s : H) ∈ (S : Subgroup H) := mem_subgroupOf.1 hs
    have hk : s⁻¹ * y ∈ Zc := by
      rw [← QuotientGroup.eq]
      exact hsy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hk
    have e : y = s * (zCent z) ^ k := by rw [hk]; group
    rw [e, Subgroup.coe_mul, Subgroup.coe_zpow]
    exact mul_mem hs (zpow_mem hzS k)
  have hzQK : (⟨zCent z, hzK⟩ : ↥Kc) ∈ (QK : Subgroup ↥Kc) := by
    rw [hmemQK]
    show π (zCent z) ∈ A₀
    rw [hπz]
    exact one_mem _
  have hinv : ∀ s : ↥(QK : Subgroup ↥Kc), orderOf s = 2 → s = ⟨⟨zCent z, hzK⟩, hzQK⟩ := by
    intro s hs
    set y : C := ((s : ↥Kc) : C)
    have hy2 : orderOf y = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hs
    have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
    have hyA : π y ∈ A₀ := (hmemQK _).1 s.2
    have hπy : π y = 1 := by
      by_contra hne
      have hord : orderOf (π y) = 2 :=
        orderOf_eq_prime (by rw [sq, ← map_mul, hyy, map_one]) hne
      have hsq := hlift y (hS y hyA) hyA hord
      have : (y : H) ^ 2 = 1 := by
        rw [sq, ← Subgroup.coe_mul, hyy, OneMemClass.coe_one]
      rw [this] at hsq
      rw [← hsq, orderOf_one] at hz2
      omega
    have hyZ : y ∈ Zc := (QuotientGroup.eq_one_iff _).1 hπy
    have hy : y = zCent z := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyZ
      rw [zpow_eq_zpow_emod' k (by rw [sq]; exact hzz)] at hk
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero] at hk
        rw [← hk, orderOf_one] at hy2
        omega
      · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one] at hk
        exact hk.symm
    exact Subtype.ext (Subtype.ext hy)
  have hatmost : CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution
      ↥(QK : Subgroup ↥Kc) := fun s t hs ht => (hinv s hs).trans (hinv t ht).symm
  have hncyc : ¬ IsCyclic ↥(QK : Subgroup ↥Kc) := by
    intro hcyc
    let ψ : ↥(QK : Subgroup ↥Kc) →* ↥(AK : Subgroup ↥K) :=
      (φ.comp (QK : Subgroup ↥Kc).subtype).codRestrict _ (fun y => by
        show φ y ∈ (AK : Subgroup ↥K)
        exact y.2)
    have hψ : Function.Surjective ψ := by
      intro a
      obtain ⟨y, hy⟩ := hφsurj (a : ↥K)
      have hyQ : y ∈ (QK : Subgroup ↥Kc) := by
        rw [Sylow.coe_comapOfKerIsPGroup, mem_comap, hy]
        exact a.2
      exact ⟨⟨y, hyQ⟩, Subtype.ext hy⟩
    haveI := isCyclic_of_surjective ψ hψ
    obtain ⟨eA⟩ := D₀.A_iso
    let e1 : ↥(AK : Subgroup ↥K) ≃* ↥A₀ :=
      ((AK : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hAKeq)
    haveI : IsCyclic (DihedralGroup (2 ^ (m - 1))) := isCyclic_of_surjective
      ((e1.trans eA).toMonoidHom) (e1.trans eA).surjective
    have h1 := (DihedralGroup.isCyclic_iff).1 this
    have : 2 ≤ 2 ^ (m - 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by have := D₀.two_le_m; omega)
    omega
  obtain ⟨r, hr, ⟨eQ⟩⟩ := (CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution QK.isPGroup'
    hatmost).resolve_left hncyc
  set Khat : Subgroup H := Kc.map C.subtype
  have hKhatC : Khat ≤ C := map_subtype_le Kc
  have hsub : Khat.subgroupOf C = Kc := comap_map_eq_self_of_injective C.subtype_injective Kc
  let e : ↥Kc ≃* ↥Khat := Kc.equivMapOfInjective C.subtype C.subtype_injective
  let Phat : Sylow 2 ↥Khat := QK.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Khat, hKhatC, hsub ▸ hKcN, ⟨zCent z, hzK, rfl⟩, Phat, r, hr, ⟨?_⟩⟩
  exact ((Subgroup.equivMapOfInjective (QK : Subgroup ↥Kc) e.toMonoidHom e.injective).symm).trans eQ

theorem footeMainAbstract_of_theorem1 (h1 : FooteTheorem1) :
    ∀ (H : Type) [Group H] [Finite H] (S : Sylow 2 H) (z : H),
      (center ↥(S : Subgroup H)).map (S : Subgroup H).subtype = zpowers z → orderOf z = 2 →
      ∀ (m n : ℕ) (D : FooteData (centralizerQuot z) (sylowQuot S z) m n),
        LiftsSquareToZ S z D.toFooteCore → CFSG.ClassicalInvolution.NormalQuaternionAt z := by
  intro H _ _ S z hZ hz2 m n D hlift
  have hSz := le_centralizer_of_center_eq hZ
  rcases h1 (centralizerQuot z) (sylowQuotSylow S hSz) m n D with hA | hA
  · exact normalQuaternionAt_of_closed S hZ hz2 D.toFooteCore hA
      (fun g hg hgA hord => hlift g hg (Or.inl hgA) hord)
  · exact normalQuaternionAt_of_closed S hZ hz2 D.toFooteCore.star hA
      (fun g hg hgA hord => hlift g hg (Or.inr hgA) hord)

end Main

end CFSG.CGT.Foote81L6
