module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1ZStar
public import CFSG.StronglyEmbedded.DihedralSylowNoStrongEmbedding

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.StronglyEmbedded

section Quotient

variable {H : Type*} [Group H] {N K : Subgroup H} [N.Normal]

theorem mk_mem_map_mk'_iff (hNK : N ≤ K) (h : H) :
    (h : H ⧸ N) ∈ K.map (QuotientGroup.mk' N) ↔ h ∈ K := by
  rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk', sup_eq_left.mpr hNK]

theorem fusionStronglyEmbedded_map_mk' [Finite H] (hNK : N ≤ K) (hK : K ≠ ⊤) {k : H}
    (hk : k ∈ K) (hkN : k ∉ N) (hkk : k * k ∈ N)
    (hfus : ∀ y h : H, y ∈ K → y ∉ N → y * y ∈ N → h * y * h⁻¹ ∈ K → h ∈ K) :
    fusionStronglyEmbedded (K.map (QuotientGroup.mk' N)) := by
  refine ⟨fun htop => hK ?_, ?_, fun g hg => ?_⟩
  · refine eq_top_iff.mpr fun h _ => (mk_mem_map_mk'_iff hNK h).mp ?_
    rw [htop]
    exact Subgroup.mem_top _
  · have h2 : orderOf (⟨(k : H ⧸ N), (mk_mem_map_mk'_iff hNK k).mpr hk⟩ :
        K.map (QuotientGroup.mk' N)) = 2 := by
      rw [Subgroup.orderOf_mk]
      refine orderOf_eq_prime ?_ fun h1 => hkN ((QuotientGroup.eq_one_iff k).mp h1)
      rw [pow_two, ← QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hkk]
    rw [even_iff_two_dvd, ← h2]
    exact orderOf_dvd_natCard _
  · by_contra hodd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    obtain ⟨hwK, hwK'⟩ := Subgroup.mem_inf.mp w.2
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (w : H ⧸ N)
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hw1 : (w : H ⧸ N) ≠ 1 := fun h1 => by
      rw [show w = 1 from Subtype.ext h1, orderOf_one] at hw
      exact absurd hw (by decide)
    have hww : (w : H ⧸ N) * w = 1 := by
      rw [← Subgroup.coe_mul, ← pow_two, ← hw, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [← hy] at hwK hwK' hw1 hww
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at hwK'
    refine hg ((mk_mem_map_mk'_iff hNK h).mpr (hfus y h ((mk_mem_map_mk'_iff hNK y).mp hwK)
      (fun hyN => hw1 ((QuotientGroup.eq_one_iff y).mpr hyN))
      ((QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_mul]; exact hww)) ?_))
    rw [← mk_mem_map_mk'_iff hNK, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    exact hwK'

end Quotient

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem S_le_centralizer_X (hb : CaseB1 Q B T L M) :
    b1S T ≤ Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)) := fun _ hs =>
  Subgroup.mem_centralizer_iff.mpr fun _ hx => (hb.commute_of_mem_X_of_mem_S hx hs).eq

theorem exists_conj_mem_S (hb : CaseB1 Q B T L M) {y : J ⧸ Subgroup.center J}
    (hy : y ∈ Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)))
    (hyy : y * y ∈ b1X T L) :
    ∃ c ∈ Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)),
      c * y * c⁻¹ ∈ b1S T := by
  have hy4 : y ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two, hb.mul_self_of_mem_X hyy]
  have hp : IsPGroup 2 (Subgroup.zpowers y) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy4)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  obtain ⟨c, hc⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_conjugate_into_sylow_within_overgroup 2
      Nat.prime_two hb.sylow _ hb.S_le_centralizer_X _ hp (Subgroup.zpowers_le.mpr hy)
  exact ⟨c, c.2, hc (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers y))⟩

theorem mem_of_conj_mem_of_mul_self_mem_X (hb : CaseB1 Q B T L M)
    {y h : J ⧸ Subgroup.center J}
    (hy : y ∈ Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)))
    (hyy : y * y ∈ b1X T L) (hyX : y ∉ b1X T L) (hyB : y ∈ b1Bar B)
    (hh : h ∈ Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)))
    (hhy : h * y * h⁻¹ ∈ b1Bar B) : h ∈ b1Bar B := by
  obtain ⟨c, hc, hcS⟩ := hb.exists_conj_mem_S hy hyy
  obtain ⟨x₀, hx₀, d, hd, hxd⟩ := hb.exists_mul_of_mem_S hcS
  have hcX := Subgroup.mem_centralizer_iff.mp hc
  have hhX := Subgroup.mem_centralizer_iff.mp hh
  have hy' : y = c⁻¹ * (x₀ * d) * c := by rw [hxd]; group
  have hd1 : d ≠ 1 := by
    rintro rfl
    refine hyX ?_
    rw [hy', mul_one, mul_assoc, hcX x₀ hx₀, inv_mul_cancel_left]
    exact hx₀
  have hdd : d * d = 1 := by
    have h1 : x₀ * d * (x₀ * d) = d * d := by
      calc x₀ * d * (x₀ * d) = x₀ * (d * x₀) * d := by group
        _ = x₀ * (x₀ * d) * d := by rw [(hb.commute_of_mem_X_of_mem_D hx₀ hd).eq]
        _ = x₀ * x₀ * (d * d) := by group
        _ = d * d := by rw [hb.mul_self_of_mem_X hx₀, one_mul]
    have h2 : x₀ * d * (x₀ * d) = y * y := by
      calc x₀ * d * (x₀ * d) = c * (y * y) * c⁻¹ := by rw [hy']; group
        _ = y * y := by rw [← hcX _ hyy, mul_inv_cancel_right]
    refine hb.eq_one_of_mem_X_of_mem_D ?_ ((b1D T L).mul_mem hd hd)
    rw [← h1, h2]
    exact hyy
  obtain ⟨x, hx, hx1, -⟩ := hb.exists_mem_X_ne (one_mem (b1X T L))
  have ha : x * x₀ ∈ b1X T L := (b1X T L).mul_mem hx hx₀
  have haB : x * x₀ ∈ b1Bar B := hb.S_le (hb.X_le_S ha)
  have hconj : c⁻¹ * (x * x₀) * c = x * x₀ := by rw [mul_assoc, hcX _ ha, inv_mul_cancel_left]
  have hmix : IsMixedInv (x * x₀ * y) := by
    have h := (isMixedInv_inv_mul_mul_iff c (x * d)).mpr
      (hb.isMixedInv_mul hx hd hx1 (orderOf_eq_prime (by rw [pow_two, hdd]) hd1))
    have heq : c⁻¹ * (x * d) * c = x * x₀ * y := by
      calc c⁻¹ * (x * d) * c = c⁻¹ * (x * x₀ * (x₀ * d)) * c := by
            rw [mul_assoc x x₀, ← mul_assoc x₀, hb.mul_self_of_mem_X hx₀, one_mul]
        _ = c⁻¹ * (x * x₀) * c * (c⁻¹ * (x₀ * d) * c) := by group
        _ = x * x₀ * y := by rw [← hy', hconj]
    rwa [heq] at h
  refine hb.setting.mem_of_conj_mem_of_isMixedInv hmix ((b1Bar B).mul_mem haB hyB) ?_
  have heq : h * (x * x₀ * y) * h⁻¹ = x * x₀ * (h * y * h⁻¹) := by
    calc h * (x * x₀ * y) * h⁻¹ = h * (x * x₀) * y * h⁻¹ := by group
      _ = x * x₀ * h * y * h⁻¹ := by rw [← hhX _ ha]
      _ = x * x₀ * (h * y * h⁻¹) := by group
  rw [heq]
  exact (b1Bar B).mul_mem haB hhy

theorem commutator_psi_symm_not_mem_X (hb : CaseB1 Q B T L M) :
    (((hb.psi.symm (1, DihedralGroup.r 1) : b1S T) : J ⧸ Subgroup.center J) *
        ((hb.psi.symm (1, DihedralGroup.sr 0) : b1S T) : J ⧸ Subgroup.center J))⁻¹ *
      (((hb.psi.symm (1, DihedralGroup.sr 0) : b1S T) : J ⧸ Subgroup.center J) *
        ((hb.psi.symm (1, DihedralGroup.r 1) : b1S T) : J ⧸ Subgroup.center J)) ∉ b1X T L := by
  intro hX
  have ha := hb.psi_symm_mem_D (DihedralGroup.r 1)
  have hd := hb.psi_symm_mem_D (DihedralGroup.sr 0)
  have h1 := hb.eq_one_of_mem_X_of_mem_D hX ((b1D T L).mul_mem
    ((b1D T L).inv_mem ((b1D T L).mul_mem ha hd)) ((b1D T L).mul_mem hd ha))
  have hS : hb.psi.symm (1, DihedralGroup.r 1) * hb.psi.symm (1, DihedralGroup.sr 0) =
      hb.psi.symm (1, DihedralGroup.sr 0) * hb.psi.symm (1, DihedralGroup.r 1) :=
    Subtype.ext (inv_mul_eq_one.mp h1)
  rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk] at hS
  exact not_commute_dihedralGroup_r_one_sr_zero (by have := hb.four_le; omega)
    (congrArg Prod.snd (hb.psi.symm.injective hS))

theorem centralizer_X_le (hb : CaseB1 Q B T L M) :
    Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)) ≤ b1Bar B := by
  by_contra hH
  have hSH := hb.S_le_centralizer_X
  let C := Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J))
  let N : Subgroup C := (b1X T L).subgroupOf C
  have : N.Normal := Subgroup.normal_of_le_center fun n hn => Subgroup.mem_center_iff.mpr
    fun g => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp g.2 _ (Subgroup.mem_subgroupOf.mp hn)).symm
  let K : Subgroup C := (b1Bar B).subgroupOf C
  have hNK : N ≤ K := fun n hn =>
    Subgroup.mem_subgroupOf.mpr (hb.S_le (hb.X_le_S (Subgroup.mem_subgroupOf.mp hn)))
  have hK : K ≠ ⊤ := fun htop => hH fun h hh => by
    have hmem : (⟨h, hh⟩ : C) ∈ K := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have huu : (u : J ⧸ Subgroup.center J) * u ∈ b1X T L := by
    rw [← pow_two, ← hb.orderOf_mk, pow_orderOf_eq_one]
    exact one_mem _
  have hSE : fusionStronglyEmbedded (K.map (QuotientGroup.mk' N)) :=
    fusionStronglyEmbedded_map_mk' hNK hK (k := ⟨u, hSH hb.mk_mem_S⟩)
      (Subgroup.mem_subgroupOf.mpr (hb.S_le hb.mk_mem_S))
      (fun h => hb.mk_not_mem_X (Subgroup.mem_subgroupOf.mp h))
      (Subgroup.mem_subgroupOf.mpr huu) fun y h hyK hyN hyy hhy => Subgroup.mem_subgroupOf.mpr
        (hb.mem_of_conj_mem_of_mul_self_mem_X y.2 (Subgroup.mem_subgroupOf.mp hyy)
          (fun h' => hyN (Subgroup.mem_subgroupOf.mpr h')) (Subgroup.mem_subgroupOf.mp hyK) h.2
          (Subgroup.mem_subgroupOf.mp hhy))
  let P : Sylow 2 (C ⧸ N) :=
    (hb.sylow.subtype hSH).mapSurjective (QuotientGroup.mk'_surjective N)
  have hmemP : ∀ s (hs : s ∈ b1S T),
      QuotientGroup.mk' N ⟨s, hSH hs⟩ ∈ (P : Subgroup (C ⧸ N)) := fun s hs => by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  let a : C := ⟨_, hSH (hb.psi.symm (1, DihedralGroup.r 1)).2⟩
  let d : C := ⟨_, hSH (hb.psi.symm (1, DihedralGroup.sr 0)).2⟩
  have hdd : d * d = 1 := Subtype.ext (by
    change ((hb.psi.symm (1, DihedralGroup.sr 0) * hb.psi.symm (1, DihedralGroup.sr 0) :
      b1S T) : J ⧸ Subgroup.center J) = 1
    rw [← map_mul, Prod.mk_mul_mk, mul_one, DihedralGroup.sr_mul_self, Prod.mk_one_one,
      map_one, Subgroup.coe_one])
  have hdN : d ∉ N := fun hdN => by
    have h1 : ((hb.psi.symm (1, DihedralGroup.sr 0) : b1S T) : J ⧸ Subgroup.center J) = 1 :=
      hb.eq_one_of_mem_X_of_mem_D (Subgroup.mem_subgroupOf.mp hdN) (hb.psi_symm_mem_D _)
    rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, Prod.mk_eq_one] at h1
    have h2 := h1.2
    rw [DihedralGroup.one_def] at h2
    cases h2
  have hd2 : orderOf (QuotientGroup.mk' N d) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hdN ((QuotientGroup.eq_one_iff d).mp h1)
    rw [pow_two, ← map_mul, hdd, map_one]
  have hc := commute_of_mem_sylow_of_fusionStronglyEmbedded hSE P
    (hmemP _ (hb.psi.symm (1, DihedralGroup.sr 0)).2) hd2
    (hmemP _ (hb.psi.symm (1, DihedralGroup.r 1)).2)
  have hker : (a * d)⁻¹ * (d * a) ∈ N := by
    rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, map_mul,
      map_mul]
    exact hc.eq
  exact hb.commutator_psi_symm_not_mem_X (Subgroup.mem_subgroupOf.mp hker)

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
