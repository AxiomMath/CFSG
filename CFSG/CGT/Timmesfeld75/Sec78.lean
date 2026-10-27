module

public import CFSG.CGT.Timmesfeld75.Sec78U
public import CFSG.CGT.Timmesfeld75.Sec78Comm
public import CFSG.CGT.Timmesfeld75.Sec78Same
public import CFSG.CGT.Timmesfeld75.Sec78Stmt
public import CFSG.CGT.Timmesfeld75.Sec78Delta

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

section Core

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem Sec6Ctx.sec78_core_model (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (h77 : Sec77) (hc : Sec6Ctx T T₁ n m)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn4 : 4 ≤ n) (hA8 : ¬ (n = 4 ∧ m = 1))
    (M : TModel T T₁ n m) {x y z : G} {k : ℕ} (hcfg : BadConfig78 T x z y k)
    (hzdef : z = x * (x * y) ^ k) : False := by
  have := hc.finite
  have hn3 : 3 ≤ n := by omega
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have hk := hcfg.odd
  have hk3 := hcfg.three
  have ho := hcfg.ord
  have hxD : x ∈ classD T := mem_classD_of_mem hcfg.xT hcfg.x1
  have hzD : z ∈ classD T := hcfg.zN.1
  have hx2 : x * x = 1 := elemAbelian_mul_self hTab hcfg.xT
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_classD hTab hcfg.yD
  have hz2 : z * z = 1 := mul_self_eq_one_of_mem_classD hTab hzD
  obtain ⟨u, fz, g, vz, hu, huT, hux, huz, huzD, hvz, hfz0, hg0, hfzv, hgv, hdz, hdu, hindg,
      hindz⟩ :=
    hc.exists_u78 h66 h1 h62 h63 hnat hn4 hA8 M hcfg
  have hu2 : u * u = 1 := mul_self_eq_one_of_mem_classD hTab hu.1
  have hxz1 : x * z ≠ 1 := by
    intro h
    apply hcfg.zT
    have h' : z = x⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h', elemAbelian_inv hTab hcfg.xT]
    exact hcfg.xT
  have hcc : (x * y) ^ k = x * z := hcfg.cz
  have hcu : u * (x * z) = (x * z) * u := by
    rw [← mul_assoc, hux, mul_assoc, huz, ← mul_assoc]
  have hcy : y * (x * z) = (x * z) * y := hcfg.yc
  have hz' : (x * y) ^ ((k + 1) / 2) * y * ((x * y) ^ ((k + 1) / 2))⁻¹ = z := by
    rw [hzdef]
    exact dih_conj hx2 hy2 hk ho
  have hg₀c : (x * y) ^ ((k + 1) / 2) * (x * z) = (x * z) * (x * y) ^ ((k + 1) / 2) := by
    rw [← hcc]
    exact ((Commute.refl (x * y)).pow_pow _ _).eq
  have hcuc : Commute (u * y) (x * z) := Commute.mul_left (show Commute u (x * z) from hcu)
    (show Commute y (x * z) from hcy)
  have hno := (sec76_of h66 h1 h62 h63) G T T₁ n m hc hnat hn3 hA8 x hxD y hcfg.yD k hk hk3 ho u
    hu.1 hux
  rcases (hc.sec73 h1 h62 h63 h66 hA8 hnat hu.1 hcfg.yD).1 with h4 | hodd | ⟨r, hr, hr2⟩
  · exact hno.2 h4
  ·
    have hh := dih_odd_conj hu2 hy2 hodd rfl
    have hhc : (u * y) ^ ((orderOf (u * y) + 1) / 2) * (x * z) =
        (x * z) * (u * y) ^ ((orderOf (u * y) + 1) / 2) := (hcuc.pow_left _).eq
    have hw : ((u * y) ^ ((orderOf (u * y) + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) * (x * z) =
        (x * z) * ((u * y) ^ ((orderOf (u * y) + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) :=
      (Commute.mul_left (show Commute _ (x * z) from hhc)
        (Commute.inv_left (show Commute _ (x * z) from hg₀c))).eq
    have he : ((u * y) ^ ((orderOf (u * y) + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) * z *
        ((u * y) ^ ((orderOf (u * y) + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹)⁻¹ = u := by
      exact conj_conj_pair_eq hz' hh
    exact hc.false_of_delta h63 h77 hnat hn3 hA8 M hcfg.xT hcfg.x1 hcfg.zN hcfg.zT hcfg.xz
      hcfg.xzD hu huT hux huz hvz hvz hdu hdz hindg hw (Or.inl he.symm)
  ·
    have hr3 : 3 ≤ r := by
      obtain ⟨a, ha⟩ := hr
      have := hno.1
      omega
    obtain ⟨hcen_u, hcen_y⟩ := dihedral_center_comm hu2 hy2 (dih_pow_two_mul hr2)
    obtain ⟨ub, hub⟩ : ∃ ub : G, ub = u * (u * y) ^ r := ⟨_, rfl⟩
    have hubconj : (u * y) ^ ((r + 1) / 2) * y * ((u * y) ^ ((r + 1) / 2))⁻¹ = ub := by
      rw [hub]
      exact dih_conj hu2 hy2 hr hr2
    have hubD : ub ∈ classD T := by
      rw [← hubconj]
      exact classD_conj_mul hcfg.yD _
    have hcuD : (u * y) ^ r ∉ classD T := fun hD =>
      hc.false_of_center_mem_D h1 h62 h63 hA8 hnat hu.1 hcfg.yD hr3 hr2 hD
    have huub : u * ub = (u * y) ^ r := by
      rw [hub, ← mul_assoc, hu2, one_mul]
    have hubu : ub * u = u * ub := by
      rw [huub, hub, mul_assoc, ← hcen_u, ← mul_assoc, hu2, one_mul]
    have hubu' : ub * u = (u * y) ^ r := by rw [hubu, huub]
    have hubc : ub * (x * z) = (x * z) * ub := by
      rw [hub]
      exact (Commute.mul_left (show Commute u (x * z) from hcu) (hcuc.pow_left r)).eq
    have hubz_ne : ub ≠ z := by
      intro h
      apply hcuD
      rw [← huub, h]
      exact huzD
    have hux1 : u * x ≠ 1 := by
      intro h
      apply huT
      rw [eq_inv_of_mul_eq_one_left h, elemAbelian_inv hTab hcfg.xT]
      exact hcfg.xT
    obtain ⟨hubx, hubz⟩ := hc.comm_of_commuting_config h66 h1 h62 h63 h77 hnat hn3 hA8 hxD hzD
      hubD hu.1 hcfg.xz hxz1 hcfg.xzD hubc hubu.symm hux huz hux1 (ne_one_of_mem_classD huzD)
      hubz_ne
    have hxcu : x * (u * y) ^ r = (u * y) ^ r * x := by
      rw [← huub]
      exact (Commute.mul_right (show Commute x u from hux.symm)
        (show Commute x ub from hubx.symm)).eq
    have hg₀cu : (x * y) ^ ((k + 1) / 2) * (u * y) ^ r = (u * y) ^ r * (x * y) ^ ((k + 1) / 2) :=
      (((show Commute x ((u * y) ^ r) from hxcu).mul_left
        (show Commute y ((u * y) ^ r) from hcen_y)).pow_left _).eq
    have hh₀cu : (u * y) ^ ((r + 1) / 2) * (u * y) ^ r = (u * y) ^ r * (u * y) ^ ((r + 1) / 2) :=
      ((Commute.refl (u * y)).pow_pow _ _).eq
    have hwc_U : ((u * y) ^ ((r + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) * (x * z) =
        (x * z) * ((u * y) ^ ((r + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) :=
      (Commute.mul_left (hcuc.pow_left _)
        (Commute.inv_left (show Commute _ (x * z) from hg₀c))).eq
    have hconjU : ub = ((u * y) ^ ((r + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) * z *
        ((u * y) ^ ((r + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹)⁻¹ := by
      exact (conj_conj_pair_eq hz' hubconj).symm
    have hconjS : z = ((x * y) ^ ((k + 1) / 2) * ((u * y) ^ ((r + 1) / 2))⁻¹) * ub *
        ((x * y) ^ ((k + 1) / 2) * ((u * y) ^ ((r + 1) / 2))⁻¹)⁻¹ := by
      exact (conj_conj_pair_eq hubconj hz').symm
    have hwc_S : ((x * y) ^ ((k + 1) / 2) * ((u * y) ^ ((r + 1) / 2))⁻¹) * (ub * u) =
        (ub * u) * ((x * y) ^ ((k + 1) / 2) * ((u * y) ^ ((r + 1) / 2))⁻¹) := by
      rw [hubu']
      exact (Commute.mul_left (show Commute _ ((u * y) ^ r) from hg₀cu)
        (Commute.inv_left (show Commute _ ((u * y) ^ r) from hh₀cu))).eq
    by_cases hubT : ub ∈ T
    ·
      have hub1 : ub ≠ 1 := ne_one_of_mem_classD hubD
      exact hc.false_of_delta h63 h77 hnat hn3 hA8 M (x := ub) (z := u) (δ := z) hubT hub1 hu huT
        hubu (by rw [hubu']; exact hcuD) hcfg.zN hcfg.zT hubz.symm huz.symm hvz hvz hdz hdu hindz
        hwc_S (Or.inr hconjS)
    · have hubN : ub ∈ normD T :=
        ⟨hubD, hTwc.centralizer_le_normalizer hcfg.xT hcfg.x1
          (Subgroup.mem_centralizer_singleton_iff.2 hubx)⟩
      obtain ⟨fb, vb, hfbv, hvb, hfb0, hdb⟩ := M.exists_data hubN hubT
      by_cases hker : ∀ w, fb w = 0 ↔ fz w = 0
      ·
        have hcc : (u * y) ^ r * (u * y) ^ r = 1 := by
          rw [← pow_add, ← two_mul]
          exact dih_pow_two_mul hr2
        have hcu1 : (u * y) ^ r ≠ 1 :=
          pow_ne_one_of_lt_orderOf (by omega) (by rw [hr2]; omega)
        have hu_eq : u = ub * (u * y) ^ r := by rw [hub, mul_assoc, hcc, mul_one]
        have hwcu : ((u * y) ^ ((r + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) * (u * y) ^ r =
            (u * y) ^ r * ((u * y) ^ ((r + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹) :=
          (Commute.mul_left (show Commute _ ((u * y) ^ r) from hh₀cu)
            (Commute.inv_left (show Commute _ ((u * y) ^ r) from hg₀cu))).eq
        have hbD : z * (u * y) ^ r ∈ classD T := by
          have := classD_conj hu.1
            (((u * y) ^ ((r + 1) / 2) * ((x * y) ^ ((k + 1) / 2))⁻¹))
          rwa [inv_conj_mul_of_commute hu_eq hconjU hwcu] at this
        have hbx : z * (u * y) ^ r * x = x * (z * (u * y) ^ r) :=
          (Commute.mul_left (show Commute z x from hcfg.xz.symm)
            (show Commute ((u * y) ^ r) x from hxcu.symm)).eq
        exact hc.false_of_same_hyperplane h66 h1 h62 h63 hnat hn3 hA8 M hcfg.xT hcfg.x1 hcfg.zN hu
          huT hubN hubT hvz hvb hgv hfbv hfzv hg0 hfb0 hdz hdu hdb hindg hker huub hubu.symm hcu1
          hcuD hbD hbx
      · exact hc.false_of_delta h63 h77 hnat hn3 hA8 M hcfg.xT hcfg.x1 hcfg.zN hcfg.zT hcfg.xz
          hcfg.xzD hubN hubT hubx hubz hvb hvz hdb hdz (indep_of_ker_ne hfb0 hfz0 hker) hwc_U
          (Or.inl hconjU)

end Core

theorem Sec6Ctx.sec78_core (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (h77 : Sec77) (hc : Sec6Ctx T T₁ n m)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn4 : 4 ≤ n) (hA8 : ¬ (n = 4 ∧ m = 1))
    {x y : G} (hxT : x ∈ T) (hx1 : x ≠ 1) (hy : y ∈ classD T) {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k)
    (ho : orderOf (x * y) = 2 * k) : False := by
  obtain ⟨hN, ε, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 hA8 hnat
  have := hN
  let M : TModel T T₁ n m := ⟨ε, φ, hcompat, htr⟩
  exact hc.sec78_core_model h66 h1 h62 h63 h77 hnat hn4 hA8 M
    (hc.badConfig_of_pair h1 h62 h63 hA8 hnat hxT hx1 hy hk hk3 ho) rfl

theorem sec78_of (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) : Sec78 := by
  have h77 : Sec77 := sec77_of h66 h1 h62 h63
  intro G _ T T₁ n m hc hnat hn4 hA8 d hd e he k hk hk3 ho
  obtain ⟨g, t, htT, ht1, hdg⟩ := hd
  have hy : g * e * g⁻¹ ∈ classD T := classD_conj_mul he g
  have hx : g * d * g⁻¹ = t := by rw [hdg]; group
  have hord : orderOf (t * (g * e * g⁻¹)) = 2 * k := by
    have e1 : t * (g * e * g⁻¹) = g * (d * e) * g⁻¹ := by rw [← hx]; group
    rw [e1]
    have := MulEquiv.orderOf_eq (MulAut.conj g) (d * e)
    simpa [MulAut.conj_apply, ho] using this
  exact hc.sec78_core h66 h1 h62 h63 h77 hnat hn4 hA8 htT ht1 hy hk hk3 hord

end CFSG.CGT.Timmesfeld75
