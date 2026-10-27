module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRk
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Cross

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

namespace OFC

theorem layer_le_of_centralizer_eq_bot {A : Type} [Group A] [Finite A] {J : Subgroup A}
    (hJ : IsComponent J) (hC : centralizer (J : Set A) = ⊥) : layer A ≤ J := by
  refine sSup_le fun J' hJ' => ?_
  rcases LocalCores.distinct_components_commute hJ hJ' with h | h
  · exact h.symm.le
  · exfalso
    have hle : J' ≤ centralizer (J : Set A) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h
    rw [hC] at hle
    obtain ⟨-, -, a, b, hab⟩ := hJ'.1
    have hsub : ∀ x : ↥J', x = 1 := fun x => Subtype.ext (by simpa using hle x.2)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [hsub a', hsub b'] at hab
    exact hab rfl

theorem isFourSubgroup_barIn {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    (hQ : IVK.IsFourSubgroup Q) (hQH : Q ≤ H) : IVK.IsFourSubgroup (barIn H Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hQ.1
  have := IsElementaryAbelian.subgroupOf (p := 2) hQH
  exact ⟨IsElementaryAbelian.map (QuotientGroup.mk' (pPrimeCore 2 ↥H)),
    by rw [L52Two.card_barIn (IsElementaryAbelian.isPGroup 2 ↥Q) hQH, hQ.2]⟩

theorem isFourSubgroup_subgroupOf {A : Type} [Group A] {Q J : Subgroup A}
    (hQ : IVK.IsFourSubgroup Q) (hQJ : Q ≤ J) : IVK.IsFourSubgroup (Q.subgroupOf J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hQ.1
  exact ⟨IsElementaryAbelian.subgroupOf hQJ,
    by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv, hQ.2]⟩

end OFC

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem btConfig_of_cell (hInv : InvSec) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} [J.Normal]
    (hJ : IsComponent J) (hJC : centralizer (J : Set (HBar H)) = ⊥)
    {Γ : Type} [Group Γ] [Finite Γ] {K : Subgroup Γ} [K.Normal] {P' : Subgroup Γ}
    (hq : IsQuasisimple ↥K) (hPp : IsPGroup p ↥P') (hTr : LinkTr H P J K P')
    (hU : innerPart (K := K) P' ≠ ⊥) : BTConfig k p (↥K ⧸ center ↥K) := by
  obtain ⟨e, he⟩ := hTr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : center ↥J = ⊥ := EL3.center_eq_bot_of_centralizer_eq_bot hJC
  let Φ : HBar H →* MulAut (↥K ⧸ center ↥K) :=
    (MulAut.congr e).toMonoidHom.comp (actYHom (K := J))
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr e).injective.comp (actYHom_injective hJC hZ)
  let ψ : ↥J →* ↥K ⧸ center ↥K := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥J))
  have hψinj : Function.Injective ψ := by
    refine e.injective.comp ?_
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hΦin : ∀ (x : HBar H) (hx : x ∈ J), Φ x = MulAut.conj (ψ ⟨x, hx⟩) := by
    intro x hx
    show MulAut.congr e (actYHom (K := J) x) = _
    rw [actYHom_of_mem hx]
    ext w
    simp [ψ, MulAut.conj_apply]
  have hΦN : ∀ h0 : ↥H, (h0 : G) ∈ normalizer (P : Set G) →
      ∃ γ ∈ normalizer (P' : Set Γ),
        Φ (QuotientGroup.mk' (pPrimeCore 2 ↥H) h0) = actYHom (K := K) γ := by
    intro h0 hh0
    obtain ⟨γ, hγ, hγe⟩ := he h0 hh0
    refine ⟨γ, hγ, ?_⟩
    ext w
    show MulAut.congr e (actYHom (K := J) (QuotientGroup.mk' (pPrimeCore 2 ↥H) h0)) w = _
    rw [OFC.congr_apply', hγe, MulEquiv.apply_symm_apply]
  have hWN : ∀ h0 : ↥H, (h0 : G) ∈ normalizer (P : Set G) →
      ∀ w ∈ innerPart (K := K) P', Φ (QuotientGroup.mk' (pPrimeCore 2 ↥H) h0) w ∈
        innerPart (K := K) P' := by
    intro h0 hh0 w hw
    obtain ⟨γ, hγ, hΦγ⟩ := hΦN h0 hh0
    rw [hΦγ]
    obtain ⟨x, hx, hxw⟩ := mem_innerPart.mp hw
    refine mem_innerPart.mpr ⟨γ * x * γ⁻¹, (Subgroup.mem_normalizer_iff.mp hγ x).mp hx, ?_⟩
    rw [map_mul, map_mul, map_inv, hxw, OFC.mul_conj_inv]
  have hIJ : barIn H I ≤ J :=
    hd.i.good.layer.trans (OFC.layer_le_of_centralizer_eq_bot hJ hJC)
  have hQJ : barIn H Q₁ ≤ J := (L52Two.barIn_mono hd.Q₁_le).trans hIJ
  have hQ₁H : Q₁ ≤ H := hd.Q₁_le.trans hd.i.good.le_H
  have hUN : L52Two.U4 z t ≤ normalizer (P : Set G) := hd.u.U_le_T.trans (T_norm h)
  have hUbar := OFC.isFourSubgroup_barIn hd.u.four (U_le_H h hd.u)
  have := hUbar.1
  refine ⟨innerPart (K := K) P', ((barIn H I).subgroupOf J).map ψ,
    ((barIn H Q₁).subgroupOf J).map ψ, (barIn H (L52Two.U4 z t)).map Φ, hU,
    isPGroup_innerPart (center_quot_eq_bot hq) hPp, ?_, ?_,
    Subgroup.map_mono (Subgroup.comap_mono (L52Two.barIn_mono hd.Q₁_le)),
    OFC.isFourSubgroup_map (OFC.isFourSubgroup_subgroupOf
      (OFC.isFourSubgroup_barIn hd.Q₁_four hQ₁H) hQJ) ψ hψinj,
    OFC.isFourSubgroup_map hUbar Φ hΦinj, ?_, ?_, ?_⟩
  · exact OFC.perfect_map (OFC.perfect_subgroupOf hIJ
      (OFC.perfect_map (OFC.perfect_subgroupOf hd.i.good.le_H hd.i.perf) _)) ψ
  · rintro _ ⟨⟨x, hxJ⟩, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_subgroupOf.mp hx :)
    refine mem_normalizer_of_conj_le fun w hw => ?_
    have h1 := hWN i (hd.i.norm_P (Subgroup.mem_subgroupOf.mp hi)) w hw
    rwa [hΦin _ hxJ, MulAut.conj_apply] at h1
  · rintro _ ⟨x, hx, rfl⟩ w hw
    obtain ⟨u, hu, rfl⟩ := hx
    exact hWN u (hUN (Subgroup.mem_subgroupOf.mp hu)) w hw
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨⟨y, hyJ⟩, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_subgroupOf.mp hy :)
    have hui : (u : G) * i = i * u :=
      hd.i.good.comm i (Subgroup.mem_subgroupOf.mp hi) u (Subgroup.mem_subgroupOf.mp hu)
    show MulAut.congr e (actYHom (K := J) _) (e _) = e _
    rw [OFC.congr_apply', MulEquiv.symm_apply_apply]
    congr 1
    show actYHom (K := J) _ (QuotientGroup.mk _) = QuotientGroup.mk _
    rw [actYHom_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show QuotientGroup.mk' (pPrimeCore 2 ↥H) u * QuotientGroup.mk' (pPrimeCore 2 ↥H) i *
      (QuotientGroup.mk' (pPrimeCore 2 ↥H) u)⁻¹ = QuotientGroup.mk' (pPrimeCore 2 ↥H) i
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hui]
    group
  · rintro _ ⟨x, hx, rfl⟩ hx1
    have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    have hx2 : orderOf x = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1'
    refine OFC.admAut_congr e fun Z _ _ hns hsec => ?_
    exact hbar_invsec hInv h.ctx H x hx2 Z hns (isSection_centralizer_of_fixSub hZ x hsec)

structure VFam (F : (Y : Type) → [Group Y] → Prop) : Prop where
  iso : ∀ {Y Y' : Type} [Group Y] [Group Y'], (Y ≃* Y') → F Y → F Y'
  bad : ∀ (k : Kind) (Y : Type) [Group Y] [Finite Y], IsClassicalKind k → F Y →
    ¬ KindFactorAll k Y
  char : ∀ (Y : Type) [Group Y] [Finite Y], F Y → ∃ r : ℕ, OddChev r Y ∧
    ¬ Nat.card Y ∣ 120 ∧ OuterFalseNS r Y ∧ ∀ k : Kind, IsClassicalKind k → ¬ BTConfig k r Y

theorem cellV_of_vfam (hInv : InvSec) (hX : Cross55)
    {F : (Y : Type) → [Group Y] → Prop} (hF : VFam F) : CellV F := by
  intro G _ _ z k S T Tstar p H P g X Y h t q I Q₁ hd J hB hFJ
  obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', hM, -, hL⟩ := hB
  have hJ : IsComponent J := by
    obtain ⟨Γ₀, _, _, π, ι, hg, -, -, -, -, -, -, -, hJ, -, -⟩ := hL
    exact hJ
  have hk := hd.u.kind
  obtain ⟨hJn, hJC, -⟩ := EL3.hbarComp_of_bad hInv h.ctx H hJ (hF.bad k _ hk hFJ)
  have := hM.normal
  obtain ⟨e, he⟩ := linkTr_of hM hL
  obtain ⟨r, hr, hcard, hOF, hBT⟩ := hF.char _ (hF.iso e hFJ)
  rcases hX p Γ V ρ K a P' hM r hr with rfl | ⟨-, h5⟩
  · by_cases hU : innerPart (K := K) P' = ⊥
    · exact false_of_innerPart_eq_bot hM hOF hU
    · exact hBT k hk (btConfig_of_cell hInv h hd hJ hJC hM.quasi hM.pgrp ⟨e, he⟩ hU)
  · exact hcard (card_dvd_of_sl2_five h5)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
