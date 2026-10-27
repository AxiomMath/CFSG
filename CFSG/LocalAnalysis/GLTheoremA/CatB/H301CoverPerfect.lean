module

import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Primitive
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

theorem perfect_comap_of_not_dvd_index {E S : Type*} [Group E] [Group S] [Finite E] {p : ℕ}
    (hp : p.Prime) (π : E →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (hkp : Nat.card π.ker = p) (hE : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤)
    {H : Subgroup S} (hH : ⁅H, H⁆ = H) (hidx : ¬ p ∣ H.index) :
    ⁅H.comap π, H.comap π⁆ = H.comap π := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  have hmap : (⁅H.comap π, H.comap π⁆).map π = H := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ, hH]
  have hsup : H.comap π = ⁅H.comap π, H.comap π⁆ ⊔ π.ker :=
    calc H.comap π = ((⁅H.comap π, H.comap π⁆).map π).comap π := by rw [hmap]
      _ = ⁅H.comap π, H.comap π⁆ ⊔ π.ker := Subgroup.comap_map_eq π _
  by_contra hle
  have hkD : ¬ π.ker ≤ ⁅H.comap π, H.comap π⁆ := fun h => hle (hsup.le.trans (sup_le le_rfl h))
  obtain ⟨z, hz, hzD⟩ := SetLike.not_le_iff_exists.1 hkD
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ H.comap π →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    rw [mul_assoc, ← Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ (hker hz) k) g₀,
      inv_mul_cancel_left]
  have hzn : z ^ (H.comap π).index ∈ ⁅H.comap π, H.comap π⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    refine Subgroup.mem_map.2 ⟨⟨_, MonoidHom.transfer_eq_pow_aux z hkey⟩, ?_, rfl⟩
    have hz' : z ∈ commutator E := by
      rw [commutator_def, hE]
      exact Subgroup.mem_top z
    rw [← Abelianization.ker_of, MonoidHom.mem_ker,
      ← MonoidHom.transfer_eq_pow (Abelianization.of : ↥(H.comap π) →* _) z hkey]
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker
      (MonoidHom.transfer (Abelianization.of : ↥(H.comap π) →* _)) hz')
  rw [Subgroup.index_comap_of_surjective H hπ] at hzn
  have hord : orderOf z ∣ p := by
    rw [← hkp]
    exact π.ker.orderOf_dvd_natCard hz
  have hcop : Nat.Coprime H.index (orderOf z) :=
    Nat.Coprime.coprime_dvd_right hord ((Nat.Prime.coprime_iff_not_dvd hp).2 hidx).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact hzD (hm ▸ Subgroup.pow_mem _ hzn m)

theorem isTypeWithCenter_layer_cover_of_quasisimple {E S : Type} [Group E] [Group S] [Finite E]
    [Finite S] (π : E →* S) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center E)
    (hk3 : Nat.card π.ker = 3) (hE : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤) {d : S}
    (hq : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({d} : Set S)))
    (hz : Nat.card (Subgroup.center ↥(Subgroup.centralizer ({d} : Set S))) = 3)
    (hidx : ¬ 3 ∣ (Subgroup.centralizer ({d} : Set S)).index)
    {Q : TauCeti.CFSGIndex → Prop}
    (hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs (↥(Subgroup.centralizer ({d} : Set S)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({d} : Set S))) Q)
    {dh : E} (hdh : π dh = d) :
    CFSG.LocalAnalysis.GLTheoremA.S8.IsTypeWithCenter 3
      (CFSG.Open.GLAPLayer 3 (Subgroup.centralizer ({dh} : Set E))) Q 9 := by
  set C := Subgroup.centralizer ({d} : Set S)
  set Ch := C.comap π with hChdef
  have hChP : Group.IsPerfect ↥Ch := Subgroup.isPerfect_iff.2
    (perfect_comap_of_not_dvd_index Nat.prime_three π hπ hker.le hk3 hE
      (Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hq.1)) hidx)
  let φ : ↥Ch →* ↥C := (π.comp Ch.subtype).codRestrict C fun x => x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := hπ y
    exact ⟨⟨e, hy⟩, rfl⟩
  have hφker : φ.ker ≤ Subgroup.center ↥Ch := by
    intro x hx
    have hx1 : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxz := Subgroup.mem_center_iff.mp (hker.le hx1)
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hxz y)
  have hZ : (Subgroup.center ↥C).comap φ = Subgroup.center ↥Ch :=
    CFSG.LocalCores.comap_center_eq_of_perfect hChP φ hφ hφker
  have hdhC : dh ∈ Ch := by
    show π dh ∈ C
    rw [hdh]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hdhZ : (⟨dh, hdhC⟩ : ↥Ch) ∈ Subgroup.center ↥Ch := by
    rw [← hZ, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : S) * π dh = π dh * g
    rw [hdh]
    exact Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hCE : Subgroup.centralizer ({dh} : Set E) = Ch := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · have hg' : g * dh = dh * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      show π g ∈ C
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [← hdh, ← map_mul, hg', map_mul]
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hdhZ ⟨g, hg⟩))
  have hC0 : 0 < C.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hcardCh : Nat.card ↥Ch = 3 * Nat.card ↥C := by
    refine Nat.eq_of_mul_eq_mul_right hC0 ?_
    have h1 := Subgroup.card_mul_index Ch
    have h2 := Subgroup.card_mul_index C
    have h3 := Subgroup.card_ker_mul_card_of_surjective hπ
    rw [hChdef, Subgroup.index_comap_of_surjective C hπ] at h1
    rw [hk3] at h3
    rw [h1, ← h3, ← h2, mul_assoc]
  have hZC0 : 0 < (Subgroup.center ↥C).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hZ9 : Nat.card (Subgroup.center ↥Ch) = 9 := by
    refine Nat.eq_of_mul_eq_mul_right hZC0 ?_
    have hidxZ : (Subgroup.center ↥Ch).index = (Subgroup.center ↥C).index := by
      rw [← hZ]
      exact Subgroup.index_comap_of_surjective _ hφ
    have h1 := Subgroup.card_mul_index (Subgroup.center ↥Ch)
    have h2 := Subgroup.card_mul_index (Subgroup.center ↥C)
    rw [hidxZ, hcardCh, ← h2, hz] at h1
    rw [h1]
    ring
  have hψker : ((QuotientGroup.mk' (Subgroup.center ↥C)).comp φ).ker = Subgroup.center ↥Ch := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ]
  let eC : (↥Ch ⧸ Subgroup.center ↥Ch) ≃* (↥C ⧸ Subgroup.center ↥C) :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hφ))
  have hqCh : CFSG.Open.IsQuasisimple ↥Ch :=
    ⟨Group.isPerfect_def.1 hChP, eC.isSimpleGroup_congr.2 hq.2⟩
  have hCn : ∀ g ∈ Ch, ∀ l ∈ Ch, g * l * g⁻¹ ∈ Ch := fun g hg l hl =>
    Ch.mul_mem (Ch.mul_mem hg hl) (Ch.inv_mem hg)
  have hp3 : 3 ∣ Nat.card ↥Ch := ⟨Nat.card ↥C, hcardCh⟩
  have hcent : IsPGroup 3 ↥(Ch ⊓ Subgroup.centralizer (Ch : Set E)) := by
    intro c
    refine ⟨2, ?_⟩
    have hc := Subgroup.mem_inf.1 c.2
    have hcZ : (⟨(c : E), hc.1⟩ : ↥Ch) ∈ Subgroup.center ↥Ch :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hc.2 g g.2)
    have h9 : (⟨⟨(c : E), hc.1⟩, hcZ⟩ : ↥(Subgroup.center ↥Ch)) ^ 9 = 1 := by
      rw [← hZ9]
      exact pow_card_eq_one'
    have h4 := congrArg (fun y : ↥(Subgroup.center ↥Ch) => ((y : ↥Ch) : E)) h9
    apply Subtype.ext
    simpa using h4
  have hcore := HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_normal_quasisimple
    Nat.prime_three le_rfl hCn hqCh hp3 hcent
  have hlayer : GLAPLayer 3 Ch = Ch := glaPLayer_eq_of_unique_glaPComponent
    (HardMathSupport.Dickson.I271.glaPComponent_of_normal_quasisimple le_rfl hCn hqCh hcore)
    fun J hJ => HardMathSupport.Dickson.I271.eq_of_glaPComponent_of_normal_quasisimple
      Nat.prime_three le_rfl hCn hqCh hcore hcent hJ
  rw [hCE, hlayer]
  let e : PQuot 3 Ch ≃* ↥Ch :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  refine ⟨⟨i, hi, ⟨((QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans eC).trans f⟩⟩,
    ?_⟩
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hZ9]

end CFSG.LocalAnalysis.GLTheoremA.H301
