module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110QCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111Na
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec113Frame (z : G) (K0 N K1 K2 Q1 Q2 : Subgroup G) : Prop where
  pair : Sec11Q8Pair z Q1 Q2
  K1_le : K1 ≤ K0
  K2_le : K2 ≤ K0
  N_le : N ≤ K0
  N_norm : ∀ k ∈ K0, ∀ n ∈ N, k * n * k⁻¹ ∈ N
  Q1_le : Q1 ≤ K1
  Q2_le : Q2 ≤ K2
  Q1_norm : ∀ k ∈ K1, ∀ q ∈ Q1, k * q * k⁻¹ ∈ Q1
  Q2_norm : ∀ k ∈ K2, ∀ q ∈ Q2, k * q * k⁻¹ ∈ Q2
  comm : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a
  decomp : ∀ g ∈ K0, ∃ n ∈ N, ∃ k ∈ K1 ⊔ K2, g = n * k
  Q_inf_N : ∀ y ∈ Q1 ⊔ Q2, y ∈ N → y = 1
  cent1 : ∀ a ∈ K1, (∀ b ∈ Q1, a * b = b * a) → a ∈ zpowers z
  cent2 : ∀ a ∈ K2, (∀ b ∈ Q2, a * b = b * a) → a ∈ zpowers z
  z_mem1 : z ∈ K1
  z_mem2 : z ∈ K2
  z_comm1 : ∀ k ∈ K1, k * z = z * k
  z_comm2 : ∀ k ∈ K2, k * z = z * k
  pocket1 : ∀ k ∈ K1, ∃ q ∈ Q1 ⊔ Q2, ∃ c ∈ K1, c ^ 3 = 1 ∧ k = q * c
  pocket2 : ∀ k ∈ K2, ∃ q ∈ Q1 ⊔ Q2, ∃ c ∈ K2, c ^ 3 = 1 ∧ k = q * c

theorem Sec113Frame.symm {z : G} {K0 N K1 K2 Q1 Q2 : Subgroup G}
    (F : Sec113Frame z K0 N K1 K2 Q1 Q2) : Sec113Frame z K0 N K2 K1 Q2 Q1 where
  pair := F.pair.symm
  K1_le := F.K2_le
  K2_le := F.K1_le
  N_le := F.N_le
  N_norm := F.N_norm
  Q1_le := F.Q2_le
  Q2_le := F.Q1_le
  Q1_norm := F.Q2_norm
  Q2_norm := F.Q1_norm
  comm a ha b hb := (F.comm b hb a ha).symm
  decomp g hg := by
    rw [sup_comm]
    exact F.decomp g hg
  Q_inf_N y hy := by
    rw [sup_comm] at hy
    exact F.Q_inf_N y hy
  cent1 := F.cent2
  cent2 := F.cent1
  z_mem1 := F.z_mem2
  z_mem2 := F.z_mem1
  z_comm1 := F.z_comm2
  z_comm2 := F.z_comm1
  pocket1 k hk := by
    rw [sup_comm]
    exact F.pocket2 k hk
  pocket2 k hk := by
    rw [sup_comm]
    exact F.pocket1 k hk

theorem sec113_conj_mem_twoCoreIn {X : Subgroup G} {x y : G} (hx : x ∈ X)
    (hy : y ∈ twoCoreIn X) : x * y * x⁻¹ ∈ twoCoreIn X := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem m hm ⟨x, hx⟩
  · simp

theorem sec113_frame [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    Sec113Frame z (secK0 t z) (oddCoreIn (secK0 t z)) K1 K2 (twoCoreIn K1) (twoCoreIn K2) := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hP5 := hp.facts.pockets5
  have hC5 := hp.facts.centZ5
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hp.r10.lK0 hctx
  have hQsup : secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 := sec10KS_twoCore_sup hP5 hC5 hpsp hctx
  have hK1 : K1 ≤ secK0 t z := le_sup_left.trans hKle
  have hK2 : K2 ≤ secK0 t z := le_sup_right.trans hKle
  exact
    { pair := sec11L1110_q8pair hp hctx
      K1_le := hK1
      K2_le := hK2
      N_le := Subgroup.map_subtype_le (CFSG.oddCore (secK0 t z))
      N_norm := fun k hk n hn => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hk hn
      Q1_le := twoCoreIn_le_self K1
      Q2_le := twoCoreIn_le_self K2
      Q1_norm := fun k hk q hq => sec113_conj_mem_twoCoreIn hk hq
      Q2_norm := fun k hk q hq => sec113_conj_mem_twoCoreIn hk hq
      comm := sec10Z_comm hP5 hpsp hctx
      decomp := fun g hg => sec11_K0_decomp hp.r10.lK0 hctx hg
      Q_inf_N := fun y hy hyN => sec11_Q_inf_oddCore (by rw [hQsup]; exact hy) hyN
      cent1 := sec10KS_cent_Qi hP5 hC5 hpsp hctx
      cent2 := sec10KS_cent_Qi hP5 hC5 hpsp hctx.swap
      z_mem1 := hctx.pocket1.1
      z_mem2 := hctx.pocket2.1
      z_comm1 := fun k hk => Subgroup.mem_centralizer_singleton_iff.mp
        (sec11_K0_le t z (hK1 hk)).2
      z_comm2 := fun k hk => Subgroup.mem_centralizer_singleton_iff.mp
        (sec11_K0_le t z (hK2 hk)).2
      pocket1 := fun k hk => by
        obtain ⟨q, c, hq, hc, hc3, hkqc⟩ := sec11_pocket_decomp hP5 hC5 hpsp hctx hk
        exact ⟨q, by rw [← hQsup]; exact hq, c, hc, hc3, hkqc⟩
      pocket2 := fun k hk => by
        obtain ⟨q, c, hq, hc, hc3, hkqc⟩ := sec11_pocket_decomp2 hP5 hC5 hpsp hctx hk
        exact ⟨q, by rw [← hQsup]; exact hq, c, hc, hc3, hkqc⟩ }

namespace Sec113Frame

variable {z : G} {K0 N K1 K2 Q1 Q2 : Subgroup G} (F : Sec113Frame z K0 N K1 K2 Q1 Q2)

include F

theorem exists_of_mem_sup {k : G} (hk : k ∈ K1 ⊔ N) : ∃ n ∈ N, ∃ k1 ∈ K1, k = n * k1 := by
  have hnorm : K1 ≤ normalizer (N : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => F.N_norm g (F.K1_le hg) n hn, fun hn => ?_⟩
    have := F.N_norm g⁻¹ (K0.inv_mem (F.K1_le hg)) _ hn
    simpa [mul_assoc] using this
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hk
  obtain ⟨n, hn, k1, hk1, rfl⟩ := Set.mem_mul.mp hk
  exact ⟨n, hn, k1, hk1, rfl⟩

theorem mem_sup_iff {k : G} :
    k ∈ K1 ⊔ N ↔ k ∈ K0 ∧ ∀ q ∈ Q2, k * q * k⁻¹ * q⁻¹ ∈ N := by
  constructor
  · intro hk
    obtain ⟨n, hn, k1, hk1, rfl⟩ := F.exists_of_mem_sup hk
    refine ⟨K0.mul_mem (F.N_le hn) (F.K1_le hk1), fun q hq => ?_⟩
    have hq2 : q ∈ K2 := F.Q2_le hq
    have hqK0 : q ∈ K0 := F.K2_le hq2
    have h1 : k1 * q = q * k1 := F.comm k1 hk1 q hq2
    have h2 : n * k1 * q * (n * k1)⁻¹ * q⁻¹ = n * (q * n⁻¹ * q⁻¹) := by
      calc n * k1 * q * (n * k1)⁻¹ * q⁻¹ = n * (k1 * q) * k1⁻¹ * n⁻¹ * q⁻¹ := by group
        _ = n * (q * k1) * k1⁻¹ * n⁻¹ * q⁻¹ := by rw [h1]
        _ = n * (q * n⁻¹ * q⁻¹) := by group
    rw [h2]
    exact N.mul_mem hn (F.N_norm q hqK0 n⁻¹ (N.inv_mem hn))
  · rintro ⟨hk0, hkq⟩
    obtain ⟨n, hn, kk, hkk, rfl⟩ := F.decomp k hk0
    obtain ⟨k1, hk1, k2, hk2, rfl⟩ := exists_mul_of_mem_sup_of_commute F.comm hkk
    have hk2z : k2 ∈ zpowers z := by
      refine F.cent2 k2 hk2 fun q hq => ?_
      have hq2 : q ∈ K2 := F.Q2_le hq
      have hq' : k2 * q * k2⁻¹ ∈ Q2 := F.Q2_norm k2 hk2 q hq
      have hq'K0 : k2 * q * k2⁻¹ ∈ K0 := F.K2_le (F.Q2_le hq')
      have hc1 : k1 * (k2 * q * k2⁻¹) = (k2 * q * k2⁻¹) * k1 := F.comm k1 hk1 _ (F.Q2_le hq')
      have h3 := hkq q hq
      have h4 : n * (k1 * k2) * q * (n * (k1 * k2))⁻¹ * q⁻¹ =
          (n * (k2 * q * k2⁻¹) * n⁻¹ * (k2 * q * k2⁻¹)⁻¹) * ((k2 * q * k2⁻¹) * q⁻¹) := by
        have e1 : n * (k1 * k2) * q * (n * (k1 * k2))⁻¹ =
            n * (k1 * (k2 * q * k2⁻¹)) * k1⁻¹ * n⁻¹ := by group
        rw [e1, hc1]
        group
      have h5 : n * (k2 * q * k2⁻¹) * n⁻¹ * (k2 * q * k2⁻¹)⁻¹ ∈ N := by
        have := F.N_norm _ hq'K0 n⁻¹ (N.inv_mem hn)
        have h6 := N.mul_mem hn this
        simpa [mul_assoc] using h6
      have h7 : (k2 * q * k2⁻¹) * q⁻¹ ∈ N := by
        have h8 := N.mul_mem (N.inv_mem h5) h3
        rw [h4] at h8
        simpa [mul_assoc] using h8
      have h9 : (k2 * q * k2⁻¹) * q⁻¹ ∈ Q1 ⊔ Q2 :=
        Q2.mul_mem hq' (Q2.inv_mem hq) |> fun h => Subgroup.mem_sup_right h
      have h10 := F.Q_inf_N _ h9 h7
      have h11 : k2 * q * k2⁻¹ = q := mul_inv_eq_one.mp h10
      calc k2 * q = (k2 * q * k2⁻¹) * k2 := by group
        _ = q * k2 := by rw [h11]
    have hk2K1 : k2 ∈ K1 := (Subgroup.zpowers_le.mpr F.z_mem1) hk2z
    have hk12 : k1 * k2 ∈ K1 := K1.mul_mem hk1 hk2K1
    have : n * (k1 * k2) ∈ N ⊔ K1 := Subgroup.mul_mem _ (Subgroup.mem_sup_left hn)
      (Subgroup.mem_sup_right hk12)
    rwa [sup_comm] at this

end Sec113Frame

end CFSG.OddStandard.SmallF3.Omega
