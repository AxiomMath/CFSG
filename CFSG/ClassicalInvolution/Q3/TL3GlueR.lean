module

public import CFSG.ClassicalInvolution.Q3.TL3GlueShape
public import CFSG.ClassicalInvolution.Q3.TL3SecOdd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

section OddCore

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_oddCoreImg_subgroupOf_iff {Q H : Subgroup Y} (hQH : Q ≤ H) (x : H) :
    x ∈ oddCoreImg (Q.subgroupOf H) ↔ (x : Y) ∈ oddCoreImg Q := by
  set e : ↥(Q.subgroupOf H) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQH with he
  have hO : (oddCore ↥(Q.subgroupOf H)).map e.toMonoidHom = oddCore ↥Q :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : e w ∈ oddCore ↥Q := hO ▸ ⟨w, hw, rfl⟩
    exact ⟨e w, this, rfl⟩
  · rintro ⟨w, hw, hwx⟩
    rw [← hO] at hw
    obtain ⟨w', hw', hw'e⟩ := hw
    refine ⟨w', hw', Subtype.ext ?_⟩
    have h1 : ((e w' : Q) : Y) = (w : Y) := congrArg Subtype.val hw'e
    have h2 : ((e w' : Q) : Y) = ((w' : H) : Y) := rfl
    show ((w' : H) : Y) = (x : Y)
    rw [← h2, h1]
    exact hwx

theorem oddCoreImg_inf_le (R H : Subgroup Y) : oddCoreImg R ⊓ H ≤ oddCoreImg (R ⊓ H) := by
  refine Balance.le_oddCoreIn_of_normalizes (inf_le_inf_right H (oddCoreImg_le R)) ?_ ?_
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨conj_mem_oddCoreImg (Subgroup.le_normalizer hg.1) hz1,
        H.mul_mem (H.mul_mem hg.2 hz2) (H.inv_mem hg.2)⟩
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, ?_⟩
      · have := conj_mem_oddCoreImg (Subgroup.le_normalizer (R.inv_mem hg.1)) hz1
        simpa [mul_assoc] using this
      · have := H.mul_mem (H.mul_mem (H.inv_mem hg.2) hz2) hg.2
        simpa [mul_assoc] using this
  · exact (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

end OddCore

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem partial_good_of_restrict {H : Subgroup Y} (htH : t ∈ H)
    (hg : GoodThreeElement (R.subgroupOf H) (⟨t, htH⟩ : H)) :
    ∃ (x : Y) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set Y) ∧ x ∈ H ∧ x ^ 3 ^ k = 1 ∧
      (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) ∧
      ∀ c ∈ Subgroup.centralizer ({t} : Set Y), c ∈ H → (∀ r ∈ R, ⁅c, r⁆ ∈ oddCoreImg R) →
        ⁅x, c⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y) ⊓ H) := by
  obtain ⟨x', k, hx'C, hx'3, ⟨r', hr', hr'n⟩, hx'D⟩ := hg
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hCH : (C ⊓ H).subgroupOf H = Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    exact ⟨fun hy => Subtype.ext hy.1, fun hy => ⟨congrArg Subtype.val hy, y.2⟩⟩
  have hRH : (R ⊓ H).subgroupOf H = R.subgroupOf H := Subgroup.inf_subgroupOf_right R H
  have hxC : (x' : Y) ∈ C := by
    have : x' ∈ (C ⊓ H).subgroupOf H := hCH ▸ hx'C
    exact (Subgroup.mem_subgroupOf.mp this).1
  refine ⟨x', k, hxC, x'.2, by simpa using congrArg Subtype.val hx'3, ⟨r', ?_, ?_⟩, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hr'
  · intro hcon
    apply hr'n
    rw [← hRH, mem_oddCoreImg_subgroupOf_iff inf_le_right]
    exact oddCoreImg_inf_le R H ⟨hcon, H.mul_mem (H.mul_mem (H.mul_mem x'.2 r'.2)
      (H.inv_mem x'.2)) (H.inv_mem r'.2)⟩
  · intro c hcC hcH hcD
    have h1 : (⟨c, hcH⟩ : H) ∈ Subgroup.centralizer ({(⟨t, htH⟩ : H)} : Set H) := by
      rw [← hCH]
      exact Subgroup.mem_subgroupOf.mpr ⟨hcC, hcH⟩
    have h2 : ∀ r ∈ R.subgroupOf H, ⁅(⟨c, hcH⟩ : H), r⁆ ∈ oddCoreImg (R.subgroupOf H) := by
      intro r hr
      rw [← hRH, mem_oddCoreImg_subgroupOf_iff inf_le_right]
      exact oddCoreImg_inf_le R H ⟨hcD r (Subgroup.mem_subgroupOf.mp hr),
        H.mul_mem (H.mul_mem (H.mul_mem hcH r.2) (H.inv_mem hcH)) (H.inv_mem r.2)⟩
    have h3 := hx'D _ h1 h2
    rw [← hCH, mem_oddCoreImg_subgroupOf_iff inf_le_right] at h3
    exact h3

theorem TightDatum.dbar_fixes_centralizer (d : TightDatum R S t) {u : Y}
    (hut : u ∈ Subgroup.centralizer ({t} : Set Y))
    (huK : (⟨u, hut⟩ : Subgroup.centralizer ({t} : Set Y)) ∈ d.act.ker) (hu2 : u * u = 1)
    {x : Y} (hxt : x ∈ Subgroup.centralizer ({t} : Set Y))
    (hxu : x ∈ Subgroup.centralizer ({u} : Set Y))
    (hx : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), c ∈ Subgroup.centralizer ({u} : Set Y) →
      (∀ r ∈ R, ⁅c, r⁆ ∈ oddCoreImg R) →
        ⁅x, c⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y) ⊓
          Subgroup.centralizer ({u} : Set Y))) :
    d.dbarAct ⟨x, hxt⟩ (d.toDbar ⟨_, huK⟩) = d.toDbar ⟨_, huK⟩ ∧
      ∀ c ∈ Subgroup.centralizer ({d.toDbar ⟨_, huK⟩} : Set d.Dbar),
        c⁻¹ * d.dbarAct ⟨x, hxt⟩ c ∈
          Balance.oddCoreIn (Subgroup.centralizer ({d.toDbar ⟨_, huK⟩} : Set d.Dbar)) := by
  classical
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  set Cu : Subgroup Y := Subgroup.centralizer ({u} : Set Y) with hCu
  set K : Subgroup C := d.act.ker with hK
  set uK : K := ⟨⟨u, hut⟩, huK⟩ with huKdef
  set ub : d.Dbar := d.toDbar uK with hub
  set xC : C := ⟨x, hxt⟩ with hxC
  have hxu' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxu
  have hfix : d.dbarAct xC ub = ub := by
    rw [hub, show d.toDbar uK = (QuotientGroup.mk uK : d.Dbar) from rfl, d.dbarAct_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    show x * u * x⁻¹ = u
    rw [hxu']
    group
  refine ⟨hfix, ?_⟩
  have hNodd : Odd (Nat.card d.oddKer) := by
    have h1 : Nat.card d.oddKer = Nat.card ((oddCore C).subgroupOf K) := rfl
    have h2 : Nat.card ((oddCore C).subgroupOf K) ∣ Nat.card (oddCore C) := by
      have := Subgroup.card_dvd_of_le (inf_le_left : oddCore C ⊓ K ≤ oddCore C)
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : oddCore C ⊓ K ≤ K)
        ).toEquiv, Subgroup.inf_subgroupOf_right] at this
    rw [h1]
    exact (QuaternionStructure.odd_natCard_oddCore C).of_dvd_nat h2
  have huK2 : uK * uK = 1 := by
    apply Subtype.ext; apply Subtype.ext
    exact hu2
  have hcent := OddQ.centralizer_mk_eq (N := d.oddKer) hNodd huK2
  set O' : Subgroup Y := oddCoreImg (C ⊓ Cu) with hO'
  set M : Subgroup K := (O'.comap C.subtype).comap K.subtype with hM
  set Mb : Subgroup d.Dbar := M.map d.toDbar with hMb
  have hMb : Mb ≤ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar)) := by
    refine Balance.le_oddCoreIn_of_normalizes ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      have hwO : ((w : C) : Y) ∈ O' := hw
      have hwCu : ((w : C) : Y) ∈ Cu := (inf_le_right : C ⊓ Cu ≤ Cu) (oddCoreImg_le _ hwO)
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hub, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext; apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hwCu
    · intro g hg
      have hg' : g ∈ (Subgroup.centralizer ({uK} : Set K)).map d.toDbar := by
        have := hcent ▸ hg
        exact this
      obtain ⟨c, hc, rfl⟩ := hg'
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hcCu : ((c : C) : Y) ∈ Cu := by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (congrArg (fun w : K => ((w : C) : Y)) h1)
      have hcCC : ((c : C) : Y) ∈ C ⊓ Cu := ⟨(c : C).2, hcCu⟩
      have hcN : ((c : C) : Y) ∈ Subgroup.normalizer (O' : Set Y) :=
        Q3.TightDatum.le_normalizer_oddCoreImg' (C ⊓ Cu) hcCC
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨c * w * c⁻¹, ?_, by simp⟩
        show (((c * w * c⁻¹ : K) : C) : Y) ∈ O'
        exact (Subgroup.mem_normalizer_iff.mp hcN _).mp hw
      · intro hz
        obtain ⟨w, hw, hwz⟩ := hz
        refine ⟨c⁻¹ * w * c, ?_, ?_⟩
        · show (((c⁻¹ * w * c : K) : C) : Y) ∈ O'
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN)
            (((w : K) : C) : Y)).mp hw
          simpa [mul_assoc] using this
        · rw [map_mul, map_mul, hwz, map_inv]
          group
    · have h1 : Nat.card Mb ∣ Nat.card M := Subgroup.card_map_dvd M d.toDbar
      have h2 : Nat.card M ∣ Nat.card O' := by
        have hinj : Function.Injective (C.subtype.comp K.subtype) :=
          C.subtype_injective.comp K.subtype_injective
        rw [← Subgroup.card_map_of_injective hinj]
        refine Subgroup.card_dvd_of_le ?_
        rintro _ ⟨w, hw, rfl⟩
        exact hw
      exact (odd_natCard_oddCoreImg _).of_dvd_nat (h1.trans h2)
  intro c hc
  have hc' : c ∈ (Subgroup.centralizer ({uK} : Set K)).map d.toDbar := hcent ▸ hc
  obtain ⟨c', hc'u, rfl⟩ := hc'
  refine hMb ⟨c'⁻¹ * MulAut.conjNormal (H := K) xC c', ?_, ?_⟩
  ·
    show (((c'⁻¹ * MulAut.conjNormal (H := K) xC c' : K) : C) : Y) ∈ O'
    have hcCu : ((c' : C) : Y)⁻¹ ∈ Cu := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hc'u
      have h2 : ((c' : C) : Y) * u = u * ((c' : C) : Y) :=
        congrArg (fun w : K => ((w : C) : Y)) h1
      exact Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr h2)
    have hcD : ∀ r ∈ R, ⁅((c' : C) : Y)⁻¹, r⁆ ∈ oddCoreImg R := by
      have := (d.mem_ker_act_iff ((c' : C)⁻¹)).mp (K.inv_mem c'.2)
      simpa using this
    have h3 := hx _ (C.inv_mem (c' : C).2) hcCu hcD
    have h4 := O'.inv_mem h3
    have h5 : (((c'⁻¹ * MulAut.conjNormal (H := K) xC c' : K) : C) : Y) =
        (⁅x, ((c' : C) : Y)⁻¹⁆)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def,
        hxC]
      group
    rw [h5]
    exact h4
  · rw [map_mul, map_inv]
    rfl

@[expose] def TightDatum.LayerRigidAt (d : TightDatum R S t) (ub : d.Dbar) : Prop :=
  (∀ K₁ K₂ : Subgroup d.Dbar, IsComponentOf K₁ ⊤ → IsComponentOf K₂ ⊤ →
    (∃ y ∈ K₁, y * ub ≠ ub * y) → (∃ y ∈ K₂, y * ub ≠ ub * y) → K₁ = K₂) ∧
  ∀ K : Subgroup d.Dbar, IsComponentOf K ⊤ → (∃ y ∈ K, y * ub ≠ ub * y) →
    ∀ (α : MulAut d.Dbar) (k : ℕ), α ^ 3 ^ k = 1 → α ub = ub →
      (∀ c ∈ Subgroup.centralizer ({ub} : Set d.Dbar),
        c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({ub} : Set d.Dbar))) →
      ∃ e ∈ K, ∀ y ∈ K, α y = e * y * e⁻¹

theorem TightDatum.good_of_section (d : TightDatum R S t) {u : Y}
    (hut : u ∈ Subgroup.centralizer ({t} : Set Y))
    (huK : (⟨u, hut⟩ : Subgroup.centralizer ({t} : Set Y)) ∈ d.act.ker) (hu2 : u * u = 1)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (hg : GoodThreeElement (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))) (⟨t, htu⟩ : _))
    (hL : d.LayerRigidAt (d.toDbar ⟨_, huK⟩)) : GoodThreeElement R t := by
  obtain ⟨x, k, hxt, hxu, hx3, hxR, hxD⟩ := partial_good_of_restrict htu hg
  obtain ⟨hfix, hC⟩ := d.dbar_fixes_centralizer hut huK hu2 hxt hxu hxD
  set xC : Subgroup.centralizer ({t} : Set Y) := ⟨x, hxt⟩ with hxC
  have hxC3 : xC ^ 3 ^ k = 1 := Subtype.ext (by simpa using hx3)
  have hδ3 : d.dbarAct xC ^ 3 ^ k = 1 := by rw [← map_pow, hxC3, map_one]
  have hub2 : d.toDbar ⟨_, huK⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨_, huK⟩ : d.act.ker) ^ 2 = 1 := by
      apply Subtype.ext; apply Subtype.ext
      simpa [sq] using hu2
    rw [this, map_one]
  have hgood := d.good_of_centralizer hxC3 hub2 hfix hC
    (fun K hK hKu => hL.2 K hK hKu _ k hδ3 hfix hC) hL.1
  have hx1 : d.act xC ≠ 1 := by
    intro h1
    obtain ⟨r, hr, hnr⟩ := hxR
    exact hnr ((d.act_eq_one_iff hxt).mp h1 r hr)
  exact d.goodThreeElement_of_good hxC3 hx1 hgood

end CFSG.ClassicalInvolution.Q3
