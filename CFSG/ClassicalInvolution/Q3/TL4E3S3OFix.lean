module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264B
public import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace E3S3O

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_normalizer_of_perm {N : Subgroup G} (hN : Odd (Nat.card N)) (T : Subgroup G)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hVN : V ≤ Subgroup.normalizer (N : Set G))
    (hperm : ∀ v ∈ V, ∃ n ∈ N, conjSub v T = conjSub n T) :
    ∃ n ∈ N, V ≤ Subgroup.normalizer ((conjSub n T : Subgroup G) : Set G) := by
  set X : Set (Subgroup G) := {M | ∃ n ∈ N, M = conjSub n T} with hX
  have hclosed : ∀ v ∈ V, ∀ M ∈ X, conjSub v M ∈ X := by
    rintro v hv _ ⟨n, hn, rfl⟩
    obtain ⟨n', hn', hvT⟩ := hperm v hv
    have hvn : v * n * v⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hVN hv) n).mp hn
    refine ⟨(v * n * v⁻¹) * n', N.mul_mem hvn hn', ?_⟩
    calc conjSub v (conjSub n T) = conjSub (v * n) T := (conjSub_mul v n T).symm
      _ = conjSub ((v * n * v⁻¹) * v) T := by congr 1; group
      _ = conjSub (v * n * v⁻¹) (conjSub v T) := conjSub_mul _ _ _
      _ = conjSub (v * n * v⁻¹) (conjSub n' T) := by rw [hvT]
      _ = conjSub ((v * n * v⁻¹) * n') T := (conjSub_mul _ _ _).symm
  let _ : MulAction V X :=
    { smul := fun v M => ⟨conjSub (v : G) M.1, hclosed v v.2 M.1 M.2⟩
      one_smul := fun M => Subtype.ext (conjSub_one M.1)
      mul_smul := fun a b M => Subtype.ext (conjSub_mul (a : G) (b : G) M.1) }
  have hodd : ¬ 2 ∣ Nat.card X := by
    have h := odd_natCard_conjSubClass hN T
    exact fun h2 => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  have hVp : IsPGroup 2 ↥V := hV
  obtain ⟨M₀, hM₀⟩ := hVp.nonempty_fixed_point_of_prime_not_dvd_card X hodd
  obtain ⟨n, hn, hMn⟩ := M₀.2
  refine ⟨n, hn, fun v hv => ?_⟩
  have hfix : conjSub (v : G) M₀.1 = M₀.1 := congrArg Subtype.val (hM₀ ⟨v, hv⟩)
  rw [hMn] at hfix
  exact mem_normalizer_iff_conjSub_eq.mpr hfix

theorem exists_isSylow2In_normalized {P B : Subgroup G} (hB : IsPGroup 2 B)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) :
    ∃ Q, IsSylow2In Q P ∧ B ≤ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨Q, hQP, hQ2, hQc, hBQ, -⟩ :=
    CFSG.RankThree.Coprime.exists_sylow_normalized (p := 2) P B hB hBP
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (P := P) (IsPGroup.of_bot (p := 2)) bot_le
  obtain ⟨k, hk⟩ := hV.2.1.exists_card_eq
  have hVd : 2 ^ k ∣ Nat.card P := hk ▸ Subgroup.card_dvd_of_le hV.1
  have hle : Nat.card V ≤ Nat.card Q := by
    rw [hk]
    exact Nat.le_of_dvd Nat.card_pos (hQc k hVd)
  exact ⟨Q, hV.of_natCard_le hQ2 hQP hle, hBQ⟩

variable {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

omit [Finite G] in
theorem secAct_eq_of_le_centralizer (hcl : ConjInvariant Ω) {s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) {M : Subgroup G}
    (hMs : M ≤ Subgroup.centralizer ({s} : Set G)) :
    ∀ m ∈ secImg Ω x M, secAct hcl hs m = m := by
  rintro _ ⟨y, hy, rfl⟩
  have hyM : (y : G) ∈ M := coreAt_le x M (Subgroup.mem_subgroupOf.mp hy)
  have hsy : s * (y : G) * s⁻¹ = y := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hMs hyM), mul_inv_cancel_right]
  have e := s26Act_mk (layerY Ω x) ⟨s, mem_normalizer_layerY hcl hs⟩ y y hsy.symm
  exact e

theorem exists_sylow_le_centralizer_of_fixed (h : TypeRFam r Ω) {s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) (hs2 : IsPGroup 2 (Subgroup.zpowers s))
    {M : Subgroup G} (hM : XMem Ω x M) (hsM : s ∈ Subgroup.normalizer (M : Set G))
    (hfix : ∀ m ∈ secImg Ω x M, secAct h.hyp.conjInvariant hs m = m) :
    ∃ Q, IsSylow2In Q M ∧ Q ≤ Subgroup.centralizer ({x} : Set G) ∧
      Q ≤ Subgroup.centralizer ({s} : Set G) := by
  have hsP : s ∈ Subgroup.normalizer (coreAt x M : Set G) := mem_normalizer_coreAt x hsM hs
  obtain ⟨Q, hQ, hQN⟩ := exists_isSylow2In_normalized hs2 (Subgroup.zpowers_le.mpr hsP)
  obtain ⟨hQM, hQx⟩ := (isSylow2In_coreAt_iff hM).mp hQ
  refine ⟨Q, hQM, hQx, fun q hq => ?_⟩
  have hqP : q ∈ coreAt x M := hQ.1 hq
  have hqY : q ∈ layerY Ω x := coreAt_le_layerY hM hqP
  have hsY := mem_normalizer_layerY h.hyp.conjInvariant hs
  have hsq : s * q * s⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQN (Subgroup.mem_zpowers s)) q).mp hq
  have hsqY : s * q * s⁻¹ ∈ layerY Ω x := (Subgroup.mem_normalizer_iff.mp hsY q).mp hqY
  have hmem : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨q, hqY⟩ :
      SecQuot Ω x) ∈ secImg Ω x M := ⟨⟨q, hqY⟩, Subgroup.mem_subgroupOf.mpr hqP, rfl⟩
  have e := s26Act_mk (layerY Ω x) ⟨s, hsY⟩ ⟨q, hqY⟩ ⟨s * q * s⁻¹, hsqY⟩ rfl
  have h2 : ((⟨s * q * s⁻¹, hsqY⟩ : ↥(layerY Ω x)) : SecQuot Ω x) =
      ((⟨q, hqY⟩ : ↥(layerY Ω x)) : SecQuot Ω x) := e.symm.trans (hfix _ hmem)
  have h3 := QuotientGroup.eq.mp h2
  have h4 : (s * q * s⁻¹)⁻¹ * q ∈ oddCoreOf (layerY Ω x) :=
    mem_oddCoreOf_iff.mpr ⟨(layerY Ω x).mul_mem ((layerY Ω x).inv_mem hsqY) hqY, by
      convert h3 using 1⟩
  have h5 : (s * q * s⁻¹)⁻¹ * q = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h4
    (hQ.2.1.to_le (Subgroup.zpowers_le.mpr (Q.mul_mem (Q.inv_mem hsq) hq)))
  have hc : s * q * s⁻¹ = q := inv_mul_eq_one.mp h5
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc q * s = s * q * s⁻¹ * s := by rw [hc]
    _ = s * q := by group

theorem exists_xMem_of_fixed (h : TypeRFam r Ω) {s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) (hs2 : s * s = 1)
    {Mb : Subgroup (SecQuot Ω x)} (hMb : Mb ∈ secFam Ω x)
    (hfix : ∀ m ∈ Mb, secAct h.hyp.conjInvariant hs m = m) :
    ∃ M, XMem Ω x M ∧ secImg Ω x M = Mb ∧ ∃ Q, IsSylow2In Q M ∧
      Q ≤ Subgroup.centralizer ({x} : Set G) ∧ Q ≤ Subgroup.centralizer ({s} : Set G) := by
  obtain ⟨M₁, hM₁, rfl⟩ := mem_secFam_iff.mp hMb
  have hcl := h.hyp.conjInvariant
  have hs2' : IsPGroup 2 (Subgroup.zpowers s) := Balance.isPGroup_zpowers_of_mul_self_eq_one hs2
  have hVN : Subgroup.zpowers s ≤ Subgroup.normalizer (oddCoreOf (layerY Ω x) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_oddCore_of_mem_normalizer
      (mem_normalizer_layerY hcl hs))
  have hperm : ∀ v ∈ Subgroup.zpowers s, ∃ n ∈ oddCoreOf (layerY Ω x),
      conjSub v M₁ = conjSub n M₁ := by
    intro v hv
    rcases Balance.Bootstrap.mem_zpowers_involution hs2 hv with rfl | rfl
    · exact ⟨1, (oddCoreOf _).one_mem, rfl⟩
    · have himg : secImg Ω x M₁ = secImg Ω x (conjSub v M₁) := by
        rw [secImg_conjSub_eq_map hcl hs]
        ext m
        constructor
        · intro hm
          exact ⟨m, hm, hfix m hm⟩
        · rintro ⟨m', hm', rfl⟩
          rw [show (secAct hcl hs).toMonoidHom m' = m' from hfix m' hm']
          exact hm'
      obtain ⟨ν, hν, hνM⟩ := exists_conj_of_secImg_eq h hM₁ (XMem.conj' hcl hM₁ hs) himg
      exact ⟨ν, mem_oddCoreOf_iff.mpr ⟨ν.2, hν⟩, hνM⟩
  obtain ⟨n, hn, hsN⟩ :=
    exists_conj_normalizer_of_perm (oddCoreOf_odd_natCard _) M₁ hs2' hVN hperm
  obtain ⟨hnY, hnO⟩ := mem_oddCoreOf_iff.mp hn
  have hM := XMem.conj' hcl hM₁ (layerY_le_centralizer hnY)
  have himg : secImg Ω x (conjSub n M₁) = secImg Ω x M₁ :=
    secImg_conj_of_mem (ν := ⟨n, hnY⟩) hnO M₁
  refine ⟨conjSub n M₁, hM, himg, ?_⟩
  exact exists_sylow_le_centralizer_of_fixed h hs hs2' hM (hsN (Subgroup.mem_zpowers s))
    (by rw [himg]; exact hfix)

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
