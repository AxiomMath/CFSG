module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510Stmt
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510Iface
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510Grp

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem lem510_cyc_weak_thm (h44 : II4_44) (h2A7 : II4_2A7) : Lem510_cyc' := by
  intro G _ _ z S K h hm b hbS hbb hfb hnb hXc
  classical
  by_cases hA : ∃ a ∈ S, orderOf a = 2 ∧ InducesFAut a K ∧ a ∉ cSec K
  · exact Or.inr hA
  left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrig : IsRigidRankOneComp z K := std6r1_comp_rigid h
  have hSN : S ≤ normalizer (K : Set G) := fun s hs => std6r1_S_normalizes h hs
  have hOK : HatOK (Hat K) := std6_hatOK h44 h.toStd6 hrig
  have hpS : IsPGroup 2 ↥S := std6r1_S_pgroup h
  obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg (std6_exists_sylow_P h.toStd6 hrig)
  let ρ : ↥S →* MulAut (Hat K) := (phiHom K).comp (Subgroup.inclusion hSN)
  have hρ : ∀ x : ↥S, ρ x = phi K (x : G) (hSN x.2) := fun x => rfl
  have hker : ρ.ker = (Qof S K).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρ, phi_eq_one_iff K (hSN x.2)]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hPS : Pof S K ≤ S := inf_le_left
  have hQS : Qof S K ≤ S := inf_le_left
  set D : Subgroup (MulAut (Hat K)) :=
    (Pbar : Subgroup (Hat K)).map (MulAut.conj : Hat K →* MulAut (Hat K)) with hDdef
  have hD : ((Pof S K).subgroupOf S).map ρ = D := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxP : (x : G) ∈ S ⊓ K := hx
      refine ⟨hatMk K ⟨(x : G), hxP.2⟩, ?_, ?_⟩
      · rw [hPbar]
        exact hatMk_mem_hatImg (inf_le_right : S ⊓ K ≤ K) hxP
      · rw [hρ]
        exact (phi_of_mem K hxP.2).symm
    · rintro ⟨y, hy, rfl⟩
      rw [hPbar] at hy
      obtain ⟨a, haP, rfl⟩ := mem_hatImg.1 hy
      refine ⟨⟨(a : G), hPS haP⟩, haP, ?_⟩
      rw [hρ]
      exact phi_of_mem K a.2
  have hMp : IsPGroup 2 ↥ρ.range := hpS.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hDM : D ≤ ρ.range := by
    rw [← hD]
    exact Subgroup.map_le_range _ _
  have hbN : b ∈ normalizer (K : Set G) := hSN hbS
  have hφ₀M : phi K b hbN ∈ ρ.range := ⟨⟨b, hbS⟩, rfl⟩
  have hφ₀F : IsFAutomorphism (Hat K) (phi K b hbN) := hfb.2
  have hφ₀2 : phi K b hbN * phi K b hbN = 1 := by
    have h1 := (phi_eq_one_iff K (mul_mem hbN hbN)).2 hbb.2
    rwa [phi_mul K hbN hbN] at h1
  have hφ₀1 : phi K b hbN ≠ 1 := fun h1 => hnb ((phi_eq_one_iff K hbN).1 h1)
  obtain ⟨r, hr⟩ := exists_rIface h2A7 hOK ρ.range hMp Pbar hDM (phi K b hbN) hφ₀M hφ₀F hφ₀2 hφ₀1
  obtain ⟨s, hs⟩ := hr.mem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hMp) ⟨r, hr.mem⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hr.ne_one (orderOf_eq_one_iff.1 (by simpa using hk))
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hN2 : orderOf r = 2 * 2 ^ k' := by rw [hk, pow_succ]; ring
  set H : ℕ := 2 ^ k' with hH
  have hHpos : 0 < H := by positivity
  have hHdiv : orderOf r / 2 = H := by rw [hN2]; exact Nat.mul_div_cancel_left H (by norm_num)
  have hρpow : ∀ i : ℕ, ρ (s ^ i) = r ^ i := fun i => by rw [map_pow, hs]
  have hcoe : ∀ i : ℕ, ((s ^ i : ↥S) : G) = (s : G) ^ i := fun i => rfl
  have hker' : ∀ x : ↥S, ρ x = 1 → (x : G) ∈ Qof S K := fun x hx =>
    (Subgroup.mem_subgroupOf.1 (hker ▸ (MonoidHom.mem_ker.2 hx) : x ∈ (Qof S K).subgroupOf S))
  have hker'' : ∀ x : ↥S, (x : G) ∈ Qof S K → ρ x = 1 := fun x hx =>
    MonoidHom.mem_ker.1 (hker ▸ (Subgroup.mem_subgroupOf.2 hx))
  have hsN : s ^ orderOf r ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, hρpow, pow_orderOf_eq_one]
  set b₁ : ↥S := s ^ H with hb₁
  have hρb₁ : ρ b₁ = r ^ H := hρpow H
  have hrH : r ^ H ≠ 1 := pow_ne_one_of_lt_orderOf hHpos.ne' (by rw [hN2]; omega)
  have hb₁b₁ : b₁ * b₁ = s ^ orderOf r := by rw [hb₁, ← pow_add, hN2]; congr 1; omega
  have hb₁F : InducesFAut (b₁ : G) K :=
    ⟨hSN b₁.2, by
      have := hr.fAut H hrH
      rwa [← hρb₁] at this⟩
  have hb₁n : (b₁ : G) ∉ cSec K := fun hc => hrH (hρb₁ ▸ hker'' b₁ ⟨b₁.2, hc⟩)
  obtain ⟨d, hdD, hφd⟩ := hr.invol _ hφ₀M hφ₀2 hφ₀1 hφ₀F
  rw [hHdiv] at hφd
  have hdD' : d ∈ D := hdD
  rw [← hD] at hdD'
  obtain ⟨p, hp, rfl⟩ := hdD'
  have hbρ : ρ ⟨b, hbS⟩ = ρ p * ρ b₁ := by
    rw [hρb₁]
    exact hφd
  have hu : ρ ((p * b₁)⁻¹ * ⟨b, hbS⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, hbρ]
    group
  set u : ↥S := (p * b₁)⁻¹ * ⟨b, hbS⟩ with hudef
  have hbeq : b = (p : G) * (b₁ : G) * (u : G) := by
    have : (⟨b, hbS⟩ : ↥S) = p * b₁ * u := by rw [hudef]; group
    exact congrArg Subtype.val this
  have huQ : (u : G) ∈ Qof S K := hker' u hu
  have hpP : (p : G) ∈ Pof S K := Subgroup.mem_subgroupOf.1 hp
  have hQX : Qof S K ≤ Qof S K ⊔ zpowers b := le_sup_left
  have hbX : b ∈ Qof S K ⊔ zpowers b := mem_sup_right (mem_zpowers b)
  have hXcomm : ∀ x ∈ Qof S K ⊔ zpowers b, ∀ y ∈ Qof S K ⊔ zpowers b, x * y = y * x := by
    intro x hx y hy
    have : IsCyclic ↥(Qof S K ⊔ zpowers b) := hXc
    let := IsCyclic.commGroup (α := ↥(Qof S K ⊔ zpowers b))
    have := mul_comm (⟨x, hx⟩ : ↥(Qof S K ⊔ zpowers b)) ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hb₁comm : ∀ q ∈ Qof S K, (b₁ : G) * q = q * (b₁ : G) := by
    intro q hq
    have e1 : b * q = q * b := hXcomm b hbX q (hQX hq)
    have e2 : (p : G) * q = q * p := comm_Pof_Qof_r1 h hpP hq
    have e3 : (u : G) * q = q * u := hXcomm u (hQX huQ) q (hQX hq)
    rw [hbeq] at e1
    have e5 : ((p : G) * b₁ * q) * u = ((p : G) * q * b₁) * u := by
      calc ((p : G) * b₁ * q) * u = (p : G) * b₁ * (q * u) := by group
        _ = (p : G) * b₁ * (u * q) := by rw [e3]
        _ = ((p : G) * b₁ * u) * q := by group
        _ = q * ((p : G) * b₁ * u) := e1
        _ = (q * p) * b₁ * u := by group
        _ = ((p : G) * q) * b₁ * u := by rw [e2]
        _ = ((p : G) * q * b₁) * u := by group
    have e6 := mul_right_cancel e5
    have e7 : (p : G) * ((b₁ : G) * q) = (p : G) * (q * b₁) := by
      calc (p : G) * ((b₁ : G) * q) = (p : G) * b₁ * q := by group
        _ = (p : G) * q * b₁ := e6
        _ = (p : G) * (q * b₁) := by group
    exact mul_left_cancel e7
  have hQcyc : IsCyclic ↥(Qof S K) := by
    have : IsCyclic ↥(Qof S K ⊔ zpowers b) := hXc
    have h1 : IsCyclic ↥((Qof S K).subgroupOf (Qof S K ⊔ zpowers b)) := Subgroup.isCyclic _
    exact (Subgroup.subgroupOfEquivOfLe hQX).isCyclic.1 h1
  have hQp : IsPGroup 2 ↥(Qof S K) := hpS.to_le hQS
  have hsNQ : ((s ^ orderOf r : ↥S) : G) ∈ Qof S K := hker' _ (MonoidHom.mem_ker.1 hsN)
  have hgen : ∀ x : ↥(Qof S K), x ∈ zpowers (⟨_, hsNQ⟩ : ↥(Qof S K)) := by
    rcases cyc2_square_or_generator hQp (⟨_, hsNQ⟩ : ↥(Qof S K)) with ⟨y, hy⟩ | hg
    · exfalso
      have hyS : (y : G) ∈ S := y.2.1
      let yS : ↥S := ⟨(y : G), hyS⟩
      have hyker : ρ yS = 1 := hker'' yS y.2
      have hcomm : b₁ * yS = yS * b₁ := Subtype.ext (hb₁comm (y : G) y.2)
      set w : ↥S := b₁ * yS⁻¹ with hw
      have hcommi : b₁ * yS⁻¹ = yS⁻¹ * b₁ := by
        have := congrArg (fun t => yS⁻¹ * t * yS⁻¹) hcomm
        simpa [mul_assoc] using this.symm
      have hww : w * w = 1 := by
        have hyG : ((y : G) * (y : G)) = ((s ^ orderOf r : ↥S) : G) :=
          congrArg Subtype.val hy
        have hyy : yS * yS = s ^ orderOf r := Subtype.ext hyG
        calc w * w = b₁ * yS⁻¹ * (b₁ * yS⁻¹) := by rw [hw]
          _ = b₁ * b₁ * (yS⁻¹ * yS⁻¹) := by
            calc b₁ * yS⁻¹ * (b₁ * yS⁻¹) = b₁ * (yS⁻¹ * b₁) * yS⁻¹ := by group
              _ = b₁ * (b₁ * yS⁻¹) * yS⁻¹ := by rw [hcommi]
              _ = b₁ * b₁ * (yS⁻¹ * yS⁻¹) := by group
          _ = s ^ orderOf r * (yS * yS)⁻¹ := by rw [hb₁b₁]; group
          _ = 1 := by rw [hyy]; group
      have hwρ : ρ w = r ^ H := by rw [hw, map_mul, map_inv, hyker, inv_one, mul_one, hρb₁]
      have hw1 : w ≠ 1 := fun h1 => hrH (by rw [← hwρ, h1, map_one])
      have hw2 : orderOf (w : G) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
      apply hA
      refine ⟨(w : G), w.2, hw2, ?_, fun hc => hrH (hwρ ▸ hker'' w ⟨w.2, hc⟩)⟩
      refine inducesFAut_of_mul_cSec hb₁F ?_
      have : (w : G) * (b₁ : G)⁻¹ = ((yS⁻¹ : ↥S) : G) := by
        have h1 : w * b₁⁻¹ = yS⁻¹ := by rw [hw, hcommi]; group
        exact congrArg Subtype.val h1
      rw [this]
      exact (hker' yS⁻¹ (by rw [map_inv, hyker, inv_one])).2
    · exact hg
  have hQF : Qof S K ≤ zpowers (s : G) := by
    intro x hx
    have h1 := hgen ⟨x, hx⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
    have h2 : x = ((s : G) ^ orderOf r) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    rw [h2, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hFS : zpowers (s : G) ≤ S := zpowers_le.2 s.2
  have hR : ∀ x : ↥S, (x : G) ∈ Pof S K ⊔ Qof S K → ρ x ∈ D := by
    intro x hx
    have hxm : x ∈ (Pof S K ⊔ Qof S K).subgroupOf S := hx
    rw [Subgroup.subgroupOf_sup hPS hQS] at hxm
    have hmap : ((Pof S K).subgroupOf S ⊔ (Qof S K).subgroupOf S).map ρ = D := by
      rw [Subgroup.map_sup, hD, ← hker, (Subgroup.map_eq_bot_iff _).2 le_rfl, sup_bot_eq]
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ρ hxm
  have hQeq : Qz S z = zpowers (s : G) ⊓ Rz S z := by
    rw [std6r1_Qz_eq h, std6r1_Rz_eq h]
    apply le_antisymm
    · intro x hx
      exact ⟨hQF hx, mem_sup_right hx⟩
    · rintro x ⟨hxF, hxR⟩
      have hxS : x ∈ S := hFS hxF
      obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hxF)
      have hxs : (⟨x, hxS⟩ : ↥S) = s ^ m := Subtype.ext hm.symm
      have hxρ : ρ ⟨x, hxS⟩ ∈ D := hR ⟨x, hxS⟩ hxR
      have h1 : ρ ⟨x, hxS⟩ = r ^ m := by rw [hxs, hρpow]
      have h2 : r ^ m = 1 := hr.inn m (h1 ▸ hxρ)
      exact hker' ⟨x, hxS⟩ (h1.trans h2)
  have hFmap : ((zpowers (s : G)).subgroupOf S).map ρ = zpowers r := by
    have h1 : (zpowers (s : G)).subgroupOf S = zpowers s := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
      · intro hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact Subgroup.mem_zpowers_iff.2 ⟨k, by simp⟩
    rw [h1, MonoidHom.map_zpowers, hs]
  have hrelI : (Pof S K ⊔ zpowers (s : G)).relIndex S = (D ⊔ zpowers r).relIndex ρ.range := by
    have h1 : (Pof S K ⊔ zpowers (s : G)).subgroupOf S =
        (Pof S K).subgroupOf S ⊔ (zpowers (s : G)).subgroupOf S := Subgroup.subgroupOf_sup hPS hFS
    have hkle : ρ.ker ≤ (Pof S K ⊔ zpowers (s : G)).subgroupOf S := by
      rw [hker]
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (mem_sup_right (hQF (Subgroup.mem_subgroupOf.1 hx)))
    have h2 := Subgroup.relIndex_map_map ρ ((Pof S K ⊔ zpowers (s : G)).subgroupOf S) ⊤
    rw [← MonoidHom.range_eq_map, sup_eq_left.2 hkle, top_sup_eq, Subgroup.relIndex_top_right]
      at h2
    have hHmap : ((Pof S K ⊔ zpowers (s : G)).subgroupOf S).map ρ = D ⊔ zpowers r := by
      rw [h1, Subgroup.map_sup, hD, hFmap]
    rw [hHmap] at h2
    exact h2.symm
  have hPz : Pz S z = Pof S K := std6r1_Pz_eq h
  have hidx : (Pz S z ⊔ zpowers (s : G)).relIndex S ≤ 2 := by
    rw [hPz, hrelI]
    exact hr.index
  have h2A7' : IsDoubleCoverOfAlt (HatT K) 7 → S = Pz S z ⊔ zpowers (s : G) := by
    intro h7
    have h1 := hr.a7 h7
    have h2 : (Pof S K ⊔ zpowers (s : G)).relIndex S = 1 := by
      rw [hrelI, h1, Subgroup.relIndex_self]
    rw [hPz]
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h2) (sup_le hPS hFS)
  have hinv : ∀ t ∈ S, orderOf t = 2 → InducesFAut t K → t ∈ Pz S z ⊔ zpowers (s : G) := by
    intro t ht ht2 htF
    by_cases htc : t ∈ cSec K
    · rw [hPz]
      exact mem_sup_right (hQF ⟨ht, htc⟩)
    · exact absurd ⟨t, ht, ht2, htF, htc⟩ hA
  have hFA : ∀ f ∈ zpowers (s : G), InducesFAut f K := by
    intro f hf
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hf)
    by_cases hri : r ^ i = 1
    · have hmem : (((s ^ i : ↥S)) : G) ∈ Qof S K := hker' (s ^ i) (by rw [hρpow]; exact hri)
      exact ivk_triv_fAut_of_std G z S h.toStd6 K hrig _ hmem.2
    · refine ⟨hSN (S.pow_mem s.2 i), ?_⟩
      have h1 := hr.fAut i hri
      rw [← hρpow i, hρ (s ^ i)] at h1
      exact h1
  exact ⟨zpowers (s : G), ⟨h, hFS, hQeq, hidx, h2A7', hinv, hFA⟩, inferInstance⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510
