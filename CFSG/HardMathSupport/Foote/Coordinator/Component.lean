module

public import CFSG.HardMathSupport.Foote.Coordinator.Shared
public import CFSG.Quasithin.H13.NQCatAffineCore
public import CFSG.Quasithin.H13.KGFactF618Gen

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M

theorem commute_of_map_commute {L Q : Type*} [Group L] [Group Q] [Finite L] {π : L →* Q}
    (hker : π.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card π.ker)) {z x : L}
    (hz : z * z = 1) (h : π z * π x = π x * π z) : z * x = x * z := by
  set c : L := z * x * z⁻¹ * x⁻¹ with hc
  have hcK : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc π z * π x * (π z)⁻¹ * (π x)⁻¹ = (π z * π x) * (π z)⁻¹ * (π x)⁻¹ := rfl
      _ = (π x * π z) * (π z)⁻¹ * (π x)⁻¹ := by rw [h]
      _ = 1 := by group
  have hcZ : c ∈ Subgroup.center L := hker hcK
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h1 : z * x * z⁻¹ = c * x := by rw [hc]; group
  have h2 : x = c * c * x := by
    have hcz : z * c * z⁻¹ = c := by
      have := Subgroup.mem_center_iff.mp hcZ z
      calc z * c * z⁻¹ = c * z * z⁻¹ := by rw [this]
        _ = c := by group
    calc x = z * (z * x * z⁻¹) * z⁻¹ := by rw [hzinv, ← mul_assoc, ← mul_assoc, hz, one_mul,
          mul_assoc, hz, mul_one]
      _ = z * (c * x) * z⁻¹ := by rw [h1]
      _ = (z * c * z⁻¹) * (z * x * z⁻¹) := by group
      _ = c * (c * x) := by rw [hcz, h1]
      _ = c * c * x := by group
  have hcc : c * c = 1 := by
    have h3 : c * c * x = 1 * x := by rw [one_mul]; exact h2.symm
    exact mul_right_cancel h3
  have hc1 : c = 1 := by
    have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hcc)
    have hdvdK : orderOf c ∣ Nat.card π.ker := by
      have := orderOf_dvd_natCard (⟨c, hcK⟩ : π.ker)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime 2 (Nat.card π.ker) := Nat.coprime_two_left.mpr hodd
    have h1' : orderOf c ∣ 1 := hcop ▸ Nat.dvd_gcd hdvd2 hdvdK
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1')
  rw [hc1, one_mul] at h1
  calc z * x = z * x * z⁻¹ * z := by group
    _ = x * z := by rw [h1]

structure InnerComp5 (Q : Type) [Group Q] (w : Q) (K : Subgroup Q) : Prop where
  ne_one : w ≠ 1
  invol : w * w = 1
  le : K ≤ Subgroup.centralizer ({w} : Set Q)
  mem : w ∈ K
  sl5 : Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
  comp : CFSG.IsComponent (K.subgroupOf (Subgroup.centralizer ({w} : Set Q)))

theorem isQuasisimple_sl25 :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact CFSG.Quasithin.H13.NQCat.isQuasisimple_SL2_of_four ⟨{0, 1, 2, 3}, rfl⟩

section FooteK

variable {Q : Type} [Group Q] {V : Type} [CommGroup V] [Finite V]
  {L Y : Subgroup (MulAut V)} {z : MulAut V} {π : ↥L →* Q}

theorem FooteK.innerComp5 (h : FooteK Q L Y z π) :
    InnerComp5 Q (π ⟨z, h.mem_L⟩) h.yHom.range := by
  have hker : π.ker ≤ Subgroup.center ↥L := h.ker.le
  have hodd : Odd (Nat.card π.ker) := by rw [h.ker]; exact h.oddZ
  have hzz : (⟨z, h.mem_L⟩ : ↥L) * ⟨z, h.mem_L⟩ = 1 := Subtype.ext h.invol
  have hz1 : (⟨z, h.mem_L⟩ : ↥L) ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
  have hYc : ∀ y : ↥Y, π ⟨z, h.mem_L⟩ * h.yHom y = h.yHom y * π ⟨z, h.mem_L⟩ := by
    intro y
    change π ⟨z, h.mem_L⟩ * π (Subgroup.inclusion h.le y) =
      π (Subgroup.inclusion h.le y) * π ⟨z, h.mem_L⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.central y y.2)
  have hle : h.yHom.range ≤ Subgroup.centralizer ({π ⟨z, h.mem_L⟩} : Set Q) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hYc y).symm
  refine
    { ne_one := ?_
      invol := by rw [← map_mul, hzz, map_one]
      le := hle
      mem := ⟨⟨z, h.mem⟩, rfl⟩
      sl5 := h.nonempty_range_equiv
      comp := ⟨?_, ?_⟩ }
  · intro h1
    have hmem : (⟨z, h.mem_L⟩ : ↥L) ∈ Subgroup.center ↥L := hker h1
    exact not_mem_center_of_involution h.oddZ hz1 hzz hmem
  ·
    obtain ⟨e⟩ := h.nonempty_range_equiv
    exact CFSG.Quasithin.H13.A5.KGF618.isQuasisimple_of_mulEquiv
      (e.symm.trans (Subgroup.subgroupOfEquivOfLe hle).symm) isQuasisimple_sl25
  ·
    set C : Subgroup (MulAut V) := L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) with hC
    let ψ : ↥C →* ↥(Subgroup.centralizer ({π ⟨z, h.mem_L⟩} : Set Q)) :=
      { toFun := fun x => ⟨π ⟨(x : MulAut V), x.2.1⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          exact ((Subgroup.mem_centralizer_singleton_iff.mp x.2.2))⟩
        map_one' := by
          apply Subtype.ext
          show π ⟨1, _⟩ = 1
          exact map_one π
        map_mul' := fun x y => by
          apply Subtype.ext
          show π ⟨(x : MulAut V) * y, _⟩ = π ⟨x, _⟩ * π ⟨y, _⟩
          rw [← map_mul]
          rfl }
    have hψ : Function.Surjective ψ := by
      rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := h.surj q
      have hcomm : π ⟨z, h.mem_L⟩ * π x = π x * π ⟨z, h.mem_L⟩ :=
        (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
      have hzx := commute_of_map_commute hker hodd hzz hcomm
      have hxC : (x : MulAut V) ∈ C := Subgroup.mem_inf.mpr ⟨x.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hzx).symm⟩
      exact ⟨⟨x, hxC⟩, rfl⟩
    have hmap : (Y.subgroupOf C).map ψ =
        h.yHom.range.subgroupOf (Subgroup.centralizer ({π ⟨z, h.mem_L⟩} : Set Q)) := by
      ext ⟨q, hq⟩
      constructor
      · rintro ⟨x, hxY, hxq⟩
        refine ⟨⟨(x : MulAut V), hxY⟩, ?_⟩
        have := congrArg Subtype.val hxq
        exact this
      · rintro ⟨y, hyq⟩
        have hyC : (y : MulAut V) ∈ C := Subgroup.mem_inf.mpr ⟨h.le y.2,
          Subgroup.mem_centralizer_singleton_iff.mpr (h.central y y.2).symm⟩
        exact ⟨⟨y, hyC⟩, y.2, Subtype.ext hyq⟩
    rw [← hmap]
    exact h.subnormal.map hψ

end FooteK

end CFSG.HardMathSupport.Foote.Coordinator
