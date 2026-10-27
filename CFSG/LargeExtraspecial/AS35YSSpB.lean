module

public import CFSG.LargeExtraspecial.AS35QCoNat
public import CFSG.LargeExtraspecial.AS35TMain
public import CFSG.LargeExtraspecial.AS35YSFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
  CFSG.Sporadic.Co2Smith AS35QCo AS35QCo.Native

namespace AS35YS

@[expose] def witA : ℕ → ℕ
  | 0 => 4484628546
  | _ => 35197122753

@[expose] def witB : ℕ → ℕ
  | 0 => 4733403267
  | _ => 12282003622

theorem wit_ok {k : ℕ} (hk : k = 0 ∨ k = 1) :
    isSp (witA k) = true ∧ isSp (witB k) = true ∧ mulc (witA k) (witA k) = idc ∧
      mulc (witB k) (witB k) = idc ∧ mulc (witA k) (repc k) = mulc (repc k) (witA k) ∧
      mulc (witB k) (repc k) = mulc (repc k) (witB k) ∧
      mulc (mulc (mulc (witA k) (witB k)) (mulc (witA k) (witB k))) (mulc (witA k) (witB k)) =
        idc ∧ mulc (witA k) (witB k) ≠ idc := by
  rcases hk with rfl | rfl <;> decide

theorem exists_inv_pair_three {τ : Sp62} (h2 : τ * τ = 1)
    (h1 : τ ≠ 1)
    (hprod : ∀ g : Sp62, orderOf (τ * (g * τ * g⁻¹)) ∈ ({1, 2, 3, 4} : Set ℕ)) :
    ∃ a b : Sp62, a * τ = τ * a ∧ b * τ = τ * b ∧ a * a = 1 ∧ b * b = 1 ∧ (a * b) ^ 3 = 1 ∧
      a * b ≠ 1 := by
  obtain ⟨k, hk, ρ, hρ, m, rfl⟩ := exists_conj_rep τ h2 h1
  have hk01 : k = 0 ∨ k = 1 := by
    have hbig : k = 2 ∨ k = 3 → False := by
      intro hk23
      obtain ⟨w, hw⟩ := exists_bigOrder_rep hk23 hρ
      have e : m * ρ * m⁻¹ * ((m * w * m⁻¹) * (m * ρ * m⁻¹) * (m * w * m⁻¹)⁻¹) =
          m * (ρ * (w * ρ * w⁻¹)) * m⁻¹ := by group
      have ho := hprod (m * w * m⁻¹)
      rw [e, show m * (ρ * (w * ρ * w⁻¹)) * m⁻¹ = MulAut.conj m (ρ * (w * ρ * w⁻¹)) from rfl,
        MulEquiv.orderOf_eq] at ho
      have hpow := pow_orderOf_eq_one (ρ * (w * ρ * w⁻¹))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
      rcases ho with ho | ho | ho | ho <;> rw [ho] at hpow <;>
        exact hw _ (by norm_num) (by norm_num) hpow
    by_contra hc
    push Not at hc
    exact hbig (by omega)
  obtain ⟨hA, hB, hAA, hBB, hAρ, hBρ, h3, hne⟩ := wit_ok hk01
  obtain ⟨α, hα, -⟩ := exists_rep hAA hAA hA
  obtain ⟨β, hβ, -⟩ := exists_rep hBB hBB hB
  have hαρ : α * ρ = ρ * α := Rep.unique (hα.mul hρ) (hAρ ▸ hρ.mul hα)
  have hβρ : β * ρ = ρ * β := Rep.unique (hβ.mul hρ) (hBρ ▸ hρ.mul hβ)
  have hαα : α * α = 1 := Rep.unique (hα.mul hα) (hAA ▸ Rep.one)
  have hββ : β * β = 1 := Rep.unique (hβ.mul hβ) (hBB ▸ Rep.one)
  have hαβ := hα.mul hβ
  have h3' : (α * β) ^ 3 = 1 := by
    have := (hαβ.mul hαβ).mul hαβ
    rw [h3] at this
    rw [pow_succ, pow_two]
    exact Rep.unique this Rep.one
  have hne' : α * β ≠ 1 := by
    intro e
    rw [e] at hαβ
    exact hne (Rep.code_eq hαβ Rep.one (mulc_lt _ _) (by decide))
  refine ⟨m * α * m⁻¹, m * β * m⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc m * α * m⁻¹ * (m * ρ * m⁻¹) = m * (α * ρ) * m⁻¹ := by group
      _ = m * (ρ * α) * m⁻¹ := by rw [hαρ]
      _ = m * ρ * m⁻¹ * (m * α * m⁻¹) := by group
  · calc m * β * m⁻¹ * (m * ρ * m⁻¹) = m * (β * ρ) * m⁻¹ := by group
      _ = m * (ρ * β) * m⁻¹ := by rw [hβρ]
      _ = m * ρ * m⁻¹ * (m * β * m⁻¹) := by group
  · calc m * α * m⁻¹ * (m * α * m⁻¹) = m * (α * α) * m⁻¹ := by group
      _ = 1 := by rw [hαα]; group
  · calc m * β * m⁻¹ * (m * β * m⁻¹) = m * (β * β) * m⁻¹ := by group
      _ = 1 := by rw [hββ]; group
  · have e : m * α * m⁻¹ * (m * β * m⁻¹) = m * (α * β) * m⁻¹ := by group
    rw [e, conj_pow, h3']
    group
  · intro e
    apply hne'
    have e' : α * β = m⁻¹ * (m * α * m⁻¹ * (m * β * m⁻¹)) * m := by group
    rw [e', e]
    group

theorem mem_of_inv_of_odd {C H : Subgroup Sp62} (hHC : H ≤ C)
    (hHn : ∀ c ∈ C, ∀ h ∈ H, c * h * c⁻¹ ∈ H) (hH : Nat.card H = 2 ^ 9)
    (hC : Nat.card C ∣ 1451520) {a : Sp62} (haC : a ∈ C) (haa : a * a = 1) : a ∈ H := by
  set H' := H.subgroupOf C with hH'
  have : H'.Normal := ⟨fun x hx c => mem_subgroupOf.mpr (hHn c c.2 x (mem_subgroupOf.mp hx))⟩
  have hH'c : Nat.card H' = 2 ^ 9 := by
    rw [hH', ← hH]
    exact Nat.card_congr (subgroupOfEquivOfLe hHC).toEquiv
  have hidx := Subgroup.card_mul_index H'
  rw [hH'c] at hidx
  have hodd : ¬ 2 ∣ H'.index := by
    intro h2
    obtain ⟨r, hr⟩ := h2
    rw [hr] at hidx
    have : 2 ^ 10 ∣ 1451520 := by
      have h1 : 2 ^ 10 ∣ Nat.card C := ⟨r, by rw [← hidx]; ring⟩
      exact h1.trans hC
    exact absurd this (by norm_num)
  set x := QuotientGroup.mk (s := H') (⟨a, haC⟩ : C) with hx
  have hx2 : orderOf x ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hx, pow_two, ← QuotientGroup.mk_mul]
    have e : (⟨a, haC⟩ : C) * ⟨a, haC⟩ = 1 := Subtype.ext haa
    rw [e, QuotientGroup.mk_one]
  have hxQ : orderOf x ∣ H'.index := orderOf_dvd_natCard x
  have hx1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hx2 with h | h
    · exact h
    · rw [h] at hxQ
      exact absurd hxQ hodd
  rw [orderOf_eq_one_iff, hx, QuotientGroup.eq_one_iff] at hx1
  exact mem_subgroupOf.mp hx1

theorem two_group_ne_three {H : Subgroup Sp62} (hH : Nat.card H = 2 ^ 9) {x : Sp62}
    (hx : x ∈ H) (h3 : x ^ 3 = 1) (hne : x ≠ 1) : False := by
  have ho1 : orderOf (⟨x, hx⟩ : H) ∣ 2 ^ 9 := hH ▸ orderOf_dvd_natCard _
  have ho2 : orderOf (⟨x, hx⟩ : H) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have ho : orderOf (⟨x, hx⟩ : H) = 1 := by
    have := Nat.dvd_gcd ho1 ho2
    rwa [show Nat.gcd (2 ^ 9) 3 = 1 by norm_num, Nat.dvd_one] at this
  rw [orderOf_eq_one_iff] at ho
  exact hne (congrArg Subtype.val ho)

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YS

theorem phi_inj_pbar_YS (hS : S.SixHyp) (θ : S.LbarAsc ≃* Sp62) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (Φ : S.Mbar →* Sp62)
    (hΦ : ∀ (l : S.O) (hl : l ∈ S.LbarAsc), Φ ⟨l, AS35QCo.lbar_le_mbar S hl⟩ = θ ⟨l, hl⟩) :
    Function.Injective (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype) := by
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hτL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc := subset_closure htD
  have hτA := AS35QCo.isTypeA_of_mem_dbar S hS htD
  obtain ⟨-, hext, -, hcent, -, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hP2 : IsPGroup 2 ((S.PbarAsc g).subgroupOf S.Mbar) :=
    IsPGroup.of_equiv hext.1 (subgroupOfEquivOfLe hPM).symm
  have : Finite ((S.PbarAsc g).subgroupOf S.Mbar) := Subtype.finite
  have : Group.IsNilpotent ((S.PbarAsc g).subgroupOf S.Mbar) := hP2.isNilpotent
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  by_contra hne
  have hnb := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype).ker ⊓
      center ((S.PbarAsc g).subgroupOf S.Mbar), y ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hnb ((Subgroup.eq_bot_iff_forall _).mpr hc)
  obtain ⟨hyk, hyc⟩ := mem_inf.mp hy
  have hyP : ((y : S.Mbar) : S.O) ∈ S.PbarAsc g := mem_subgroupOf.mp y.2
  have hyc' : ∀ z ∈ S.PbarAsc g, ((y : S.Mbar) : S.O) * z = z * ((y : S.Mbar) : S.O) := by
    intro z hz
    have := mem_center_iff.mp hyc ⟨⟨z, hPM hz⟩, mem_subgroupOf.mpr hz⟩
    exact (congrArg (fun w : (S.PbarAsc g).subgroupOf S.Mbar => ((w : S.Mbar) : S.O))
      this).symm
  rcases hcent _ hyP hyc' with h0 | h0
  · exact hy1 (Subtype.ext (Subtype.ext h0))
  · apply hτA.2.1
    have h1 : θ ⟨S.ρ ⟨_, htM⟩, hτL⟩ = 1 := by
      rw [← hΦ _ hτL]
      have e : (⟨S.ρ ⟨_, htM⟩, AS35QCo.lbar_le_mbar S hτL⟩ : S.Mbar) = (y : S.Mbar) :=
        Subtype.ext h0.symm
      rw [e]
      exact hyk
    have h2 := θ.injective (h1.trans (map_one θ).symm)
    exact congrArg (fun x : S.LbarAsc => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h2

theorem phi_pbar_normal_YS (hS : S.SixHyp) (θ : S.LbarAsc ≃* Sp62) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (Φ : S.Mbar →* Sp62)
    (hΦ : ∀ (l : S.O) (hl : l ∈ S.LbarAsc), Φ ⟨l, AS35QCo.lbar_le_mbar S hl⟩ = θ ⟨l, hl⟩)
    (hτL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc) (l : S.LbarAsc)
    (hc : θ l * θ ⟨_, hτL⟩ = θ ⟨_, hτL⟩ * θ l)
    (x : (S.PbarAsc g).subgroupOf S.Mbar) :
    θ l * Φ (x : S.Mbar) * (θ l)⁻¹ ∈ (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype).range := by
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hlτ : (l : S.O) * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * l := by
    have e : θ (l * ⟨_, hτL⟩) = θ (⟨_, hτL⟩ * l) := by
      simp only [map_mul]
      exact hc
    exact congrArg Subtype.val (θ.injective e)
  have hlM := AS35QCo.lbar_le_mbar S l.2
  have hmem := hnorm l hlM hlτ _ (mem_subgroupOf.mp x.2)
  refine ⟨⟨⟨_, hPM hmem⟩, mem_subgroupOf.mpr hmem⟩, ?_⟩
  calc (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype) ⟨⟨_, hPM hmem⟩, mem_subgroupOf.mpr hmem⟩
        = Φ (⟨l, hlM⟩ * (x : S.Mbar) * (⟨l, hlM⟩ : S.Mbar)⁻¹) := rfl
    _ = Φ (⟨l, hlM⟩ * (x : S.Mbar)) * Φ ((⟨l, hlM⟩ : S.Mbar)⁻¹) := Φ.map_mul _ _
    _ = Φ ⟨l, hlM⟩ * Φ (x : S.Mbar) * (Φ ⟨l, hlM⟩)⁻¹ :=
        congrArg₂ (· * ·) (Φ.map_mul _ _) (Φ.map_inv _)
    _ = θ l * Φ (x : S.Mbar) * (θ l)⁻¹ :=
        congrArg (fun y => y * Φ (x : S.Mbar) * y⁻¹) (hΦ l l.2)

theorem phi_pbar_le_YS (hS : S.SixHyp) (θ : S.LbarAsc ≃* Sp62) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (Φ : S.Mbar →* Sp62)
    (hΦ : ∀ (l : S.O) (hl : l ∈ S.LbarAsc), Φ ⟨l, AS35QCo.lbar_le_mbar S hl⟩ = θ ⟨l, hl⟩)
    (hτL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc) :
    (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype).range ≤
      centralizer ({θ ⟨_, hτL⟩} : Set Sp62) := by
  obtain ⟨-, hext, -, hcent, -, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  obtain ⟨hτc, -⟩ := AS35QCo.pbar_facts S hext hcent
  rintro _ ⟨x, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have hx := hτc _ (mem_subgroupOf.mp x.2)
  change Φ (x : S.Mbar) * θ ⟨_, hτL⟩ = θ ⟨_, hτL⟩ * Φ (x : S.Mbar)
  rw [← hΦ _ hτL, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hx

theorem false_of_sylow_YS (hS : S.SixHyp)
    (hst : S.Asc512Standing) (θ : S.LbarAsc ≃* Sp62) (hZ : center S.LbarAsc = ⊥) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (hcard : Nat.card (S.PbarAsc g) = 2 ^ 9) : False := by
  obtain ⟨Φ, hΦ⟩ := AS35QCo.exists_retraction S hst θ hZ
  have hinj := phi_inj_pbar_YS hS θ ht htM Φ hΦ
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hτL : S.ρ ⟨_, htM⟩ ∈ S.LbarAsc := subset_closure htD
  have hτA := AS35QCo.isTypeA_of_mem_dbar S hS htD
  have hPM : S.PbarAsc g ≤ S.Mbar := map_le_range _ _
  have hprod := AS35QCo.orderOf_mem_of_typeA S θ hτL hτA
  have hττ : θ ⟨_, hτL⟩ * θ ⟨_, hτL⟩ = 1 := by
    rw [← map_mul, ← map_one θ]
    congr 1
    exact Subtype.ext (Subtype.ext hτA.2.2.1)
  have hτ1 : θ ⟨_, hτL⟩ ≠ 1 := fun h => hτA.2.1 (by
    have h2 := θ.injective (h.trans (map_one θ).symm)
    exact congrArg (fun x : S.LbarAsc => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h2)
  have hHcard : Nat.card (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype).range = 2 ^ 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← hcard]
    exact Nat.card_congr (subgroupOfEquivOfLe hPM).toEquiv
  have hHC := phi_pbar_le_YS hS θ ht htM Φ hΦ hτL
  have hHn : ∀ c ∈ centralizer ({θ ⟨_, hτL⟩} : Set Sp62),
      ∀ h ∈ (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype).range,
        c * h * c⁻¹ ∈ (Φ.comp ((S.PbarAsc g).subgroupOf S.Mbar).subtype).range := by
    intro c hc h hh
    obtain ⟨x, hx⟩ := hh
    obtain ⟨l, hl⟩ := θ.surjective c
    rw [mem_centralizer_singleton_iff, ← hl] at hc
    have key := phi_pbar_normal_YS hS θ ht htM Φ hΦ hτL l hc x
    rw [hl] at key
    rw [← hx]
    exact key
  have hCdvd : Nat.card (centralizer ({θ ⟨_, hτL⟩} : Set Sp62)) ∣ 1451520 :=
    ⟨_, (card_centralizer_mul_ncard (θ ⟨_, hτL⟩)).symm⟩
  obtain ⟨a, b, haτ, hbτ, haa, hbb, h3, hne⟩ := exists_inv_pair_three hττ hτ1 hprod
  have haH := mem_of_inv_of_odd hHC hHn hHcard hCdvd (mem_centralizer_singleton_iff.mpr haτ) haa
  have hbH := mem_of_inv_of_odd hHC hHn hHcard hCdvd (mem_centralizer_singleton_iff.mpr hbτ) hbb
  exact two_group_ne_three hHcard (mul_mem haH hbH) h3 hne

end Setting

end CFSG.LargeExtraspecial
