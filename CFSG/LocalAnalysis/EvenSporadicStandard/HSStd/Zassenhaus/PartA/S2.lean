module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2W

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open
open scoped commutatorElement

section S2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_sup_of_normalizer {E : Subgroup G} {t g : G}
    (hEt : ∀ e ∈ E, e * t = t * e) (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hgt : g * t = t * g)
    {n : G} (hn : n ∈ zpowers t ⊔ E) : g * n * g⁻¹ ∈ zpowers t ⊔ E := by
  obtain ⟨i, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup hEt hn
  have h1 : g * t ^ i * g⁻¹ = t ^ i := by
    have : Commute g (t ^ i) := (show Commute g t from hgt).zpow_right i
    exact this.mul_inv_cancel
  have : g * (t ^ i * e) * g⁻¹ = t ^ i * (g * e * g⁻¹) := by
    calc g * (t ^ i * e) * g⁻¹ = (g * t ^ i * g⁻¹) * (g * e * g⁻¹) := by group
      _ = t ^ i * (g * e * g⁻¹) := by rw [h1]
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left (zpow_mem (mem_zpowers t) i))
    (Subgroup.mem_sup_right (hg e he))

theorem s2 : StepS2 := by
  intro G _ _ L t E W z hb a
  have hyL : a.y ∈ L := a.y_mem.2
  have hyt : a.y * t = t * a.y := mem_centralizer_iff.1 hb.t_cent a.y hyL
  have htcy : t ∈ Cen a.y := mem_Cen.2 hyt.symm
  have hEt : ∀ e ∈ E, e * t = t * e := by
    intro e he
    have : e ∈ centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) := by
      rw [hb.cent_tE]
      exact Subgroup.mem_sup_right he
    exact (mem_centralizer_iff.1 this t (Subgroup.mem_sup_left (mem_zpowers t))).symm
  have hKy : ∀ k ∈ a.K₀, k * a.y = a.y * k := fun k hk => mem_Cen.1 (a.K₀_le hk).2
  have hKL : ∀ k ∈ a.K₀, k ∈ L := fun k hk => (a.K₀_le hk).1
  have hynorm : a.y ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G) := by
    have hyE := Subgroup.mem_set_normalizer_iff.1 a.y_mem.1
    have hfwd : ∀ e ∈ E, a.y * e * a.y⁻¹ ∈ E := fun e he => (hyE e).1 he
    have hbwd : ∀ e ∈ E, a.y⁻¹ * e * a.y⁻¹⁻¹ ∈ E := by
      intro e he
      rw [inv_inv]
      exact (hyE (a.y⁻¹ * e * a.y)).2 (by simpa [mul_assoc] using he)
    have hyt' : a.y⁻¹ * t = t * a.y⁻¹ :=
      ((show Commute a.y t from hyt).inv_left)
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    refine ⟨fun hn => conj_mem_sup_of_normalizer hEt hfwd hyt hn, fun hn => ?_⟩
    have := conj_mem_sup_of_normalizer hEt hbwd hyt' hn
    simpa [mul_assoc] using this
  have htnorm : t ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_sup_left (mem_zpowers t))
  have hWD : WData E W t a.y :=
    { t_sq := hb.t_mul_t
      y_ord := a.y_ord
      yt := hyt
      W_comm := by
        have := hb.W_ab.1
        intro p hp q hq
        exact setLike_mul_comm hp hq
      E_le := hb.E_le_W
      E_t := hEt
      t_nmem := hb.t_nmem_W
      tW := fun w hw => hb.W_inv t htnorm w hw
      yW := fun w hw => hb.W_inv a.y hynorm w hw
      wt_mem := fun w hw =>
        (Subgroup.mem_set_normalizer_iff.1 (hb.W_le hw) t).1
          (Subgroup.mem_sup_left (mem_zpowers t))
      cent := hb.cent_tE
      W_card := hb.W_card
      E_card := hb.E_card }
  have hW16 : Nat.card ↥(W ⊓ Cen a.y) = 16 := hWD.card_cent a.card_Ey
  have hz2 : z * z = 1 := by
    have := hb.E_ab.2 z hb.z_mem
    rwa [pow_two] at this
  have hz1 : z ≠ 1 := by
    intro hz
    have hbot : E = ⊥ := by
      rw [eq_bot_iff_forall]
      intro e he
      by_contra hne
      obtain ⟨c, -, hc⟩ := hb.E_trans e he hne
      rw [hz] at hc
      apply hne
      rw [← hc]
      group
    have := hb.E_card
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hzy : z * a.y = a.y * z := a.zy.symm
  obtain ⟨k₀, hk₀W, hk₀y, hk₀z⟩ := hWD.lift hb.z_mem a.zy
  have hk₀ : k₀ * t * k₀⁻¹ = t * z := by
    have h1 : k₀ * t * k₀⁻¹ = z * t := by
      have := mul_inv_eq_iff_eq_mul.1 hk₀z
      exact this
    rw [h1]
    exact hEt z hb.z_mem
  let yX : ↥(Cen a.y) := ⟨a.y, mem_Cen.2 rfl⟩
  let tX : ↥(Cen a.y) := ⟨t, htcy⟩
  let zX : ↥(Cen a.y) := ⟨z, mem_Cen.2 hzy⟩
  let k₀X : ↥(Cen a.y) := ⟨k₀, mem_Cen.2 hk₀y.symm⟩
  let K : Subgroup ↥(Cen a.y) := a.K₀.subgroupOf (Cen a.y)
  have hK₀C : a.K₀ ≤ Cen a.y := fun k hk => (a.K₀_le hk).2
  have hdecomp : ∀ g ∈ Cen a.y, g * t = t * g →
      ∃ n j : ℤ, ∃ k ∈ a.K₀, g = t ^ n * (a.y ^ j * k) := by
    intro g hgy hgt
    have hg : g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hgt
    rw [hb.inner, sup_comm] at hg
    obtain ⟨n, l, hl, rfl⟩ := exists_zpow_mul_of_mem_sup
      (fun l hl => mem_centralizer_iff.1 hb.t_cent l hl) hg
    have hcn : Commute a.y (t ^ n) := (show Commute a.y t from hyt).zpow_right n
    have hcg : Commute a.y (t ^ n * l) := (mem_Cen.1 hgy).symm
    have hcl : Commute a.y l := by
      have := hcn.inv_right.mul_right hcg
      have e : (t ^ n)⁻¹ * (t ^ n * l) = l := by group
      rwa [e] at this
    have hlC : l ∈ L ⊓ Cen a.y := ⟨hl, mem_Cen.2 hcl.symm⟩
    rw [a.K₀_y] at hlC
    obtain ⟨j, k, hk, rfl⟩ := exists_zpow_mul_of_mem_sup hKy hlC
    exact ⟨n, j, k, hk, rfl⟩
  have hcentX : centralizer ({tX} : Set ↥(Cen a.y)) = zpowers tX ⊔ (zpowers yX ⊔ K) := by
    apply le_antisymm
    · intro x hx
      have hxt : (x : G) * t = t * x := by
        have := mem_centralizer_singleton_iff.1 hx
        exact congrArg Subtype.val this
      obtain ⟨n, j, k, hk, hxe⟩ := hdecomp x x.2 hxt
      have hkC : k ∈ Cen a.y := hK₀C hk
      have : x = tX ^ n * (yX ^ j * ⟨k, hkC⟩) := by
        apply Subtype.ext
        simpa using hxe
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left (zpow_mem (mem_zpowers tX) n))
        (Subgroup.mem_sup_right (mul_mem (Subgroup.mem_sup_left (zpow_mem (mem_zpowers yX) j))
          (Subgroup.mem_sup_right (show (⟨k, hkC⟩ : ↥(Cen a.y)) ∈ K from hk))))
    · refine sup_le ?_ (sup_le ?_ ?_)
      · rw [Subgroup.zpowers_le]
        exact mem_centralizer_singleton_iff.2 rfl
      · rw [Subgroup.zpowers_le]
        exact mem_centralizer_singleton_iff.2 (Subtype.ext hyt)
      · intro k hk
        exact mem_centralizer_singleton_iff.2
          (Subtype.ext (mem_centralizer_iff.1 hb.t_cent k.1 (hKL k.1 hk)))
  have hLD : LocalData yX tX K :=
    { y_cent := fun x => Subtype.ext (mem_Cen.1 x.2)
      y_ord := by
        have h1 := Subgroup.orderOf_coe yX
        exact h1.symm.trans a.y_ord
      t_sq := Subtype.ext hb.t_mul_t
      t_ne := by
        intro h
        have h1 : t = 1 := congrArg Subtype.val h
        have := hb.t_ord
        rw [h1, orderOf_one] at this
        omega
      K_t := fun k hk => Subtype.ext (mem_centralizer_iff.1 hb.t_cent k.1 (hKL k.1 hk))
      K_S5 := ⟨(Subgroup.subgroupOfEquivOfLe hK₀C).trans a.eK₀⟩
      cent_t := hcentX }
  have hzp : ∀ u : ↥(Cen a.y), u ∈ zpowers yX → (u : G) ∈ zpowers a.y := by
    intro u hu
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hu
    exact ⟨m, by simp [yX]⟩
  have hO : ∀ g ∈ fusionOddCoreOf (Cen a.y), ∃ x : ↥(Cen a.y),
      x ∈ fusionOddCore ↥(Cen a.y) ∧ (x : G) = g := by
    rintro g ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hrank : ∃ B : Subgroup (OQuot (Cen a.y)), IsElemAbelian 2 B ∧ Nat.card B = 16 := by
    refine exists_elemAbelian_quot ((W ⊓ Cen a.y).subgroupOf (Cen a.y)) ⟨?_, ?_⟩ ?_
    · have := hb.W_ab.1
      refine ⟨⟨fun p q => ?_⟩⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hWD.W_comm _ p.2.1 _ q.2.1
    · intro x hx
      apply Subtype.ext
      have := hb.W_ab.2 (x : G) hx.1
      simpa using this
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        W ⊓ Cen a.y ≤ Cen a.y)).toEquiv, hW16]
  exact ⟨{ toPA0 := a
           t_cy := htcy
           y_O := ⟨yX, hLD.y_mem_O, rfl⟩
           O_cent_t := by
             apply le_antisymm
             · rintro g ⟨hgO, hgt⟩
               obtain ⟨x, hxO, rfl⟩ := hO g hgO
               have hxc : x ∈ centralizer ({tX} : Set ↥(Cen a.y)) :=
                 mem_centralizer_singleton_iff.2 (Subtype.ext (mem_Cen.1 hgt))
               have : x ∈ fusionOddCore ↥(Cen a.y) ⊓ centralizer ({tX} : Set ↥(Cen a.y)) :=
                 ⟨hxO, hxc⟩
               rw [hLD.O_inf_cent] at this
               exact hzp x this
             · intro g hg
               obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
               refine ⟨⟨yX ^ m, zpow_mem hLD.y_mem_O m, by simp [yX]⟩, ?_⟩
               exact mem_Cen.2 ((((show Commute a.y t from hyt).zpow_left m)).symm.symm)
           O_inv := by
             intro o ho
             obtain ⟨x, hxO, rfl⟩ := hO o ho
             have := hzp _ (hLD.O_inv_comm.1 x hxO)
             simpa [tX] using this
           O_comm := by
             intro o₁ ho₁ o₂ ho₂
             obtain ⟨x₁, hx₁, rfl⟩ := hO o₁ ho₁
             obtain ⟨x₂, hx₂, rfl⟩ := hO o₂ ho₂
             have := hzp _ (hLD.O_inv_comm.2 x₁ hx₁ x₂ hx₂)
             simpa [commutatorElement_def] using this
           oddcore_D := fusionOddCore_quotient_eq_bot' ↥(Cen a.y)
           zstar_D := hLD.zstar_bot (z := zX) (k₀ := k₀X) (Subtype.ext hz2)
             (fun h => hz1 (congrArg Subtype.val h)) (Subtype.ext hk₀)
           Kbar_cent := hLD.cent_quot
           Kbar_disj := hLD.disj
           Kbar_card := hLD.K_card
           rank4_D := hrank }⟩

end S2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
