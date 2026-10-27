module

public import CFSG.HardMathSupport.Foote.Coordinator.Interface

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M
open scoped commutatorElement

theorem sq_eq_one_of_mem_center_sl25 {A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) : A ^ 2 = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  apply Subtype.ext
  rw [sq, Matrix.SpecialLinearGroup.coe_mul, ← hrA, Matrix.SpecialLinearGroup.coe_one, ← map_mul,
    ← sq, hr2, map_one]

section FooteK

variable {Q : Type} [Group Q] {V : Type} [CommGroup V] [Finite V]
  {L Y : Subgroup (MulAut V)} {z : MulAut V} {π : ↥L →* Q}

theorem FooteK.mem_L (h : FooteK Q L Y z π) : z ∈ L :=
  h.le h.mem

theorem FooteK.subgroupOf_inf_center (h : FooteK Q L Y z π) :
    Y.subgroupOf L ⊓ Subgroup.center ↥L = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxY, hxZ⟩
  rw [Subgroup.mem_bot]
  obtain ⟨e⟩ := h.sl5
  have hxc : (⟨(x : MulAut V), hxY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.mp hxZ ⟨(g : MulAut V), h.le g.2⟩
    have h2 : (g : MulAut V) * (x : MulAut V) = (x : MulAut V) * g := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hsq : (⟨(x : MulAut V), hxY⟩ : ↥Y) ^ 2 = 1 := by
    have hmap : e ⟨(x : MulAut V), hxY⟩ ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨_, hxc, rfl⟩
    have := sq_eq_one_of_mem_center_sl25 hmap
    rw [← map_pow, ← map_one e] at this
    exact e.injective this
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hsq
    simpa using this
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have hdvdZ : orderOf x ∣ Nat.card ↥(Subgroup.center ↥L) := by
    have := orderOf_dvd_natCard (⟨x, hxZ⟩ : ↥(Subgroup.center ↥L))
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime 2 (Nat.card ↥(Subgroup.center ↥L)) :=
    Nat.coprime_two_left.mpr h.oddZ
  have h1 : orderOf x ∣ 1 := hcop ▸ Nat.dvd_gcd hdvd2 hdvdZ
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

@[expose] noncomputable def FooteK.yHom (_h : FooteK Q L Y z π) : ↥Y →* Q :=
  π.comp (Subgroup.inclusion _h.le)

theorem FooteK.yHom_injective (h : FooteK Q L Y z π) : Function.Injective h.yHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hker : Subgroup.inclusion h.le y ∈ π.ker := hy
  rw [h.ker] at hker
  have hmem : Subgroup.inclusion h.le y ∈ Y.subgroupOf L ⊓ Subgroup.center ↥L :=
    ⟨by simp [Subgroup.mem_subgroupOf], hker⟩
  rw [h.subgroupOf_inf_center, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have := congrArg Subtype.val hmem
  simpa using this

theorem FooteK.nonempty_range_equiv (h : FooteK Q L Y z π) :
    Nonempty (↥h.yHom.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  obtain ⟨e⟩ := h.sl5
  exact ⟨(MonoidHom.ofInjective h.yHom_injective).symm.trans e⟩

theorem FooteK.dvd_card (h : FooteK Q L Y z π) : 120 ∣ Nat.card Q := by
  have hY : Nat.card ↥h.yHom.range = 120 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective h.yHom_injective).toEquiv]
    exact card_ysl5 h.sl5
  rw [← hY]
  exact Subgroup.card_subgroup_dvd_card _

end FooteK

theorem end415K_of_not_dvd {Q : Type} [Group Q] (hQ : ¬ 120 ∣ Nat.card Q) : End415K Q :=
  fun _ _ _ _ _ _ _ h => hQ h.dvd_card

theorem end415K_of_coverInv {Q : Type} [Group Q] (hcov : CoverInv Q) : End415K Q := by
  intro V _ _ L Y z π hK
  have hV := hK.elem
  have hzL : z ∈ L := hK.mem_L
  have hW := hK.commZ
  have hzz := hK.invol
  have e : (↥L ⧸ Subgroup.center ↥L) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hK.ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hK.surj)
  have hz1L : (⟨z, hzL⟩ : ↥L) ≠ 1 := fun h1 => hK.ne_one (congrArg Subtype.val h1)
  have hz2L : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := Subtype.ext hzz
  let ρ : ↥L →* MulAut V := L.subtype
  have hρ : Function.Injective ρ := Subgroup.subtype_injective _
  rcases hcov ↥L hK.quasi hK.oddZ ⟨e⟩ ⟨z, hzL⟩ hz1L hz2L with
    ⟨Φ, hΦi, hΦinv⟩ | ⟨X, Y', hX5, hY5', hZX, hZY, hZ1, hinv⟩
  · refine false_of_inverted_C55 hV hzz hW (ρ.comp Φ) (hρ.comp hΦi) fun u => ?_
    have := congrArg ρ (hΦinv u)
    simpa [ρ] using this
  · have hx5 : (ρ X) ^ 5 = 1 := by rw [← map_pow, hX5, map_one]
    have hy5 : (ρ Y') ^ 5 = 1 := by rw [← map_pow, hY5', map_one]
    have hzx : Commute ⁅ρ Y', ρ X⁆ (ρ X) := by
      rw [← map_commutatorElement]
      exact hZX.map ρ
    have hzy : Commute ⁅ρ Y', ρ X⁆ (ρ Y') := by
      rw [← map_commutatorElement]
      exact hZY.map ρ
    have hz1' : ⁅ρ Y', ρ X⁆ ≠ 1 := by
      rw [← map_commutatorElement]
      intro h1
      exact hZ1 (hρ (h1.trans (map_one ρ).symm))
    have hinv' : z * ρ X * z⁻¹ = (ρ X)⁻¹ := by
      have := congrArg ρ hinv
      simpa [ρ] using this
    have hxle : Nat.card (commSub (ρ X)) ≤ 16 := by
      have h1 := card_commSub_le_of_inverted hzz hinv' hx5
      have h2 : Nat.card (commSub z) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hW 2
      omega
    have hx1 : ρ X ≠ 1 := fun h1 => hz1' (by rw [h1, commutatorElement_one_right])
    exact false_of_heisenberg (i := 1) (j := 0) (k := 0) hx5 hy5 hzx hzy hz1' hV
      (by simpa using hx5) (by simpa using hx1) (by simpa using hxle)

end CFSG.HardMathSupport.Foote.Coordinator
