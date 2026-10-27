module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56ASEb

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable def conjAutOf (N A : Subgroup G)
    (hA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A) (n : ↥N) : MulAut ↥A where
  toFun a := ⟨(n : G) * (a : G) * (n : G)⁻¹, hA n n.2 a a.2⟩
  invFun a := ⟨(n : G)⁻¹ * (a : G) * (n : G), by
    simpa using hA _ (N.inv_mem n.2) a a.2⟩
  left_inv a := by ext; group
  right_inv a := by ext; group
  map_mul' a b := by
    apply Subtype.ext
    show (n : G) * ((a * b : ↥A) : G) * (n : G)⁻¹ =
      ((n : G) * (a : G) * (n : G)⁻¹) * ((n : G) * (b : G) * (n : G)⁻¹)
    rw [Subgroup.coe_mul]
    group

private noncomputable def conjAutHomOf (N A : Subgroup G)
    (hA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A) : ↥N →* MulAut ↥A where
  toFun := conjAutOf N A hA
  map_one' := by ext a; simp [conjAutOf]
  map_mul' n m := by
    ext a
    change (n : G) * (m : G) * (a : G) * ((n : G) * (m : G))⁻¹ =
      (n : G) * ((m : G) * (a : G) * (m : G)⁻¹) * (n : G)⁻¹
    group

private theorem conjAutHomOf_apply (N A : Subgroup G)
    (hA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A) (n : ↥N) (a : ↥A) :
    ((conjAutHomOf N A hA n a : ↥A) : G) = (n : G) * (a : G) * (n : G)⁻¹ := rfl

private theorem mul_comm_of_sq_eq_one {M : Type*} [Group M] (h : ∀ x : M, x ^ 2 = 1)
    (a b : M) : a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using h a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using h b)
  have hab : (a * b)⁻¹ = a * b :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two, mul_assoc] using h (a * b))
  calc a * b = (a * b)⁻¹ := hab.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha, hb]

theorem ase_split_sub {Q X₀ Y N E : Subgroup G} (φ : G → G) (hQX : Q ≤ X₀) (hXY : X₀ ≤ Y)
    (hQn : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hsq : ∀ y ∈ Y, y ^ 2 ∈ Q)
    (hNY : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) (hNQ : ∀ n ∈ N, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q)
    (hNE : ∀ n ∈ N, ∀ f ∈ E, n * f * n⁻¹ ∈ E)
    (hNX : ∀ n ∈ N, ∀ x ∈ X₀, ⁅n, x⁆ ∈ Q)
    (hφmul : ∀ y ∈ Y, ∀ y' ∈ Y, φ (y * y') = φ y * φ y') (hφmem : ∀ y ∈ Y, φ y ∈ E)
    (hφker : ∀ y ∈ Y, (φ y = 1 ↔ y ∈ X₀)) (hφsurj : ∀ f ∈ E, ∃ y ∈ Y, φ y = f)
    (hφconj : ∀ n ∈ N, ∀ y ∈ Y, φ (n * y * n⁻¹) = n * φ y * n⁻¹)
    (hE : IsE 3 ↥E) {z : G} (hz : z ∈ E) (hz1 : z ≠ 1) (hzfix : ∀ n ∈ N, n * z * n⁻¹ = z)
    (htrans : ∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → a ≠ z → b ≠ 1 → b ≠ z → ∃ n ∈ N, n * a * n⁻¹ = b)
    (hpairs : ∀ a ∈ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, a ≠ 1 → a ≠ z → b ≠ 1 → b ≠ z → a ≠ b →
      a ≠ b * z → a' ≠ 1 → a' ≠ z → b' ≠ 1 → b' ≠ z → a' ≠ b' → a' ≠ b' * z →
      ∃ n ∈ N, n * a * n⁻¹ = a' ∧ n * b * n⁻¹ = b')
    {wz : G} (hwzY : wz ∈ Y) (hwzφ : φ wz = z) (hwzfix : ∀ n ∈ N, ⁅n, wz⁆ ∈ Q)
    {v₀ : G} (hv₀ : v₀ ∈ E) (hv₀1 : v₀ ≠ 1) (hv₀z : v₀ ≠ z)
    {w₀ : G} (hw₀Y : w₀ ∈ Y) (hw₀φ : φ w₀ = v₀)
    (hw₀fix : ∀ n ∈ N, n * v₀ * n⁻¹ = v₀ → ⁅n, w₀⁆ ∈ Q)
    {a : G} (haN : a ∈ N) (hav₀ : a * v₀ * a⁻¹ = z * v₀) (haw₀ : wz⁻¹ * ⁅a, w₀⁆ ∈ Q) :
    ∃ M : Subgroup G, Q ≤ M ∧ M ≤ Y ∧ (∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) ∧ M ⊓ X₀ = Q ∧
      M ⊔ X₀ = Y ∧ wz ∈ M := by
  have hQY : Q ≤ Y := hQX.trans hXY
  let Qy : Subgroup ↥Y := Q.subgroupOf Y
  haveI : Qy.Normal :=
    (Subgroup.normal_subgroupOf_iff hQY).mpr fun h k hh hk => hQn k hk h hh
  let conjY : ↥N →* MulAut ↥Y := conjAutHomOf N Y hNY
  let conjE : ↥N →* MulAut ↥E := conjAutHomOf N E hNE
  have he (n : ↥N) : Qy.map (conjY n : ↥Y →* ↥Y) = Qy := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      exact hNQ n n.2 a ha
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨(conjY n)⁻¹ x, ?_, MulEquiv.apply_symm_apply (conjY n) x⟩
      rw [← map_inv conjY n]
      exact hNQ _ (N.inv_mem n.2) x hx
  let actH : ↥N →* MulAut (↥Y ⧸ Qy) :=
    { toFun n := QuotientGroup.congr Qy Qy (conjY n) (he n)
      map_one' := by
        ext w
        induction w using QuotientGroup.induction_on with
        | H y =>
          change (((conjY 1 : MulAut ↥Y) y : ↥Y) : ↥Y ⧸ Qy) = (y : ↥Y ⧸ Qy)
          rw [map_one]
          rfl
      map_mul' n m := by
        ext w
        induction w using QuotientGroup.induction_on with
        | H y =>
          change (((conjY (n * m) : MulAut ↥Y) y : ↥Y) : ↥Y ⧸ Qy) =
            (((conjY n : MulAut ↥Y) ((conjY m : MulAut ↥Y) y) : ↥Y) : ↥Y ⧸ Qy)
          rw [map_mul, MulAut.mul_apply] }
  let phiY : ↥Y →* ↥E :=
    { toFun y := ⟨φ (y : G), hφmem (y : G) y.2⟩
      map_one' := Subtype.ext ((hφker (1 : G) Y.one_mem).mpr X₀.one_mem)
      map_mul' y y' := Subtype.ext (hφmul (y : G) y.2 (y' : G) y'.2) }
  have hker : Qy ≤ phiY.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    exact Subtype.ext ((hφker (q : G) q.2).mpr (hQX (Subgroup.mem_subgroupOf.mp hq)))
  let pi : (↥Y ⧸ Qy) →* ↥E := QuotientGroup.lift Qy phiY hker
  have hπ : Function.Surjective pi := by
    intro f
    obtain ⟨y, hy, hφy⟩ := hφsurj (f : G) f.2
    exact ⟨QuotientGroup.mk' Qy ⟨y, hy⟩, Subtype.ext hφy⟩
  have hπact : ∀ (n : ↥N) (w : ↥Y ⧸ Qy), pi (actH n w) = conjE n (pi w) := by
    intro n w
    induction w using QuotientGroup.induction_on with
    | H y =>
      change phiY (conjY n y) = conjE n (phiY y)
      exact Subtype.ext (hφconj (n : G) n.2 (y : G) y.2)
  have hWexp : ∀ w : ↥Y ⧸ Qy, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H y =>
      rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [pow_two] using hsq (y : G) y.2
  have hWcomm : ∀ w v : ↥Y ⧸ Qy, w * v = v * w := fun w v => mul_comm_of_sq_eq_one hWexp w v
  have hV8 : Nat.card ↥E = 8 := by rw [hE.2]; norm_num
  have hU : ∀ (n : ↥N) (u : ↥Y ⧸ Qy), u ∈ pi.ker → actH n u = u := by
    intro n u hu
    induction u using QuotientGroup.induction_on with
    | H y =>
      have hyX : (y : G) ∈ X₀ := by
        have h1 : phiY y = 1 := MonoidHom.mem_ker.mp hu
        exact (hφker (y : G) y.2).mp (Subtype.ext_iff.mp h1)
      change QuotientGroup.mk (conjY n y) = QuotientGroup.mk y
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      have hcoe : ((conjY n y : ↥Y) : G) = (n : G) * (y : G) * (n : G)⁻¹ :=
        conjAutHomOf_apply N Y hNY n y
      rw [show ((conjY n y / y : ↥Y) : G) = ((conjY n y : ↥Y) : G) * (y : G)⁻¹ from by
        rw [Subgroup.coe_div, div_eq_mul_inv], hcoe]
      exact hNX (n : G) n.2 (y : G) hyX
  let z' : ↥E := ⟨z, hz⟩
  have hz1' : z' ≠ 1 := fun h => hz1 (Subtype.ext_iff.mp h)
  have hzfix' : ∀ n : ↥N, conjE n z' = z' := by
    intro n
    apply Subtype.ext
    change (n : G) * z * (n : G)⁻¹ = z
    exact hzfix (n : G) n.2
  have htrans' : ∀ a b : ↥E, a ≠ 1 → a ≠ z' → b ≠ 1 → b ≠ z' →
      ∃ n : ↥N, conjE n a = b := by
    intro a b ha haz hb hbz
    obtain ⟨n, hnN, hna⟩ :=
      htrans (a : G) a.2 (b : G) b.2
        (fun h => ha (Subtype.ext h)) (fun h => haz (Subtype.ext h))
        (fun h => hb (Subtype.ext h)) (fun h => hbz (Subtype.ext h))
    exact ⟨⟨n, hnN⟩, Subtype.ext hna⟩
  have hcommE : ∀ x y : ↥E, x * y = y * x := by
    haveI : IsMulCommutative (⊤ : Subgroup ↥E) := hE.1.1
    intro x y
    exact setLike_mul_comm (s := (⊤ : Subgroup ↥E))
      (show x ∈ (⊤ : Subgroup ↥E) from trivial) (show y ∈ (⊤ : Subgroup ↥E) from trivial)
  have hpairs' : ∀ a b a' b' : ↥E, a ≠ 1 → a ≠ z' → b ≠ 1 → b ≠ z' → a ≠ b → a ≠ z' * b →
      a' ≠ 1 → a' ≠ z' → b' ≠ 1 → b' ≠ z' → a' ≠ b' → a' ≠ z' * b' →
      ∃ n : ↥N, conjE n a = a' ∧ conjE n b = b' := by
    intro a b a' b' ha haz hb hbz hab hazb ha' ha'z hb' hb'z ha'b' ha'zb'
    have hnab : (a : G) ≠ (b : G) := fun h => hab (Subtype.ext h)
    have hnazb : (a : G) ≠ (b : G) * z := by
      intro h
      apply hazb
      apply Subtype.ext
      have hcoe : ((z' * b : ↥E) : G) = (b : G) * z := by
        rw [hcommE z' b, Subgroup.coe_mul]
      rw [hcoe]
      exact h
    have hna'b' : (a' : G) ≠ (b' : G) := fun h => ha'b' (Subtype.ext h)
    have hna'zb' : (a' : G) ≠ (b' : G) * z := by
      intro h
      apply ha'zb'
      apply Subtype.ext
      have hcoe : ((z' * b' : ↥E) : G) = (b' : G) * z := by
        rw [hcommE z' b', Subgroup.coe_mul]
      rw [hcoe]
      exact h
    obtain ⟨n, hnN, hna, hnb⟩ :=
      hpairs (a : G) a.2 (b : G) b.2 (a' : G) a'.2 (b' : G) b'.2
        (fun h => ha (Subtype.ext h)) (fun h => haz (Subtype.ext h))
        (fun h => hb (Subtype.ext h)) (fun h => hbz (Subtype.ext h))
        hnab hnazb
        (fun h => ha' (Subtype.ext h)) (fun h => ha'z (Subtype.ext h))
        (fun h => hb' (Subtype.ext h)) (fun h => hb'z (Subtype.ext h))
        hna'b' hna'zb'
    exact ⟨⟨n, hnN⟩, Subtype.ext hna, Subtype.ext hnb⟩
  let wzY : ↥Y := ⟨wz, hwzY⟩
  let w0Y : ↥Y := ⟨w₀, hw₀Y⟩
  let v0' : ↥E := ⟨v₀, hv₀⟩
  let wz' : ↥Y ⧸ Qy := QuotientGroup.mk wzY
  let w0' : ↥Y ⧸ Qy := QuotientGroup.mk w0Y
  have hwzπ : pi wz' = z' := Subtype.ext hwzφ
  have hwzfix' : ∀ n : ↥N, actH n wz' = wz' := by
    intro n
    change QuotientGroup.mk (conjY n wzY) = QuotientGroup.mk wzY
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have hcoe : ((conjY n wzY : ↥Y) : G) = (n : G) * wz * (n : G)⁻¹ :=
      conjAutHomOf_apply N Y hNY n wzY
    rw [show ((conjY n wzY / wzY : ↥Y) : G) = ((conjY n wzY : ↥Y) : G) * wz⁻¹ from by
      rw [Subgroup.coe_div, div_eq_mul_inv], hcoe]
    exact hwzfix (n : G) n.2
  have hv01' : v0' ≠ 1 := fun h => hv₀1 (Subtype.ext_iff.mp h)
  have hv0z' : v0' ≠ z' := fun h => hv₀z (Subtype.ext_iff.mp h)
  have hw0π : pi w0' = v0' := Subtype.ext hw₀φ
  have hw0fix' : ∀ n : ↥N, conjE n v0' = v0' → actH n w0' = w0' := by
    intro n hfix
    have hG : (n : G) * v₀ * (n : G)⁻¹ = v₀ := by
      have h2 := Subtype.ext_iff.mp hfix
      change (n : G) * v₀ * (n : G)⁻¹ = v₀ at h2
      exact h2
    change QuotientGroup.mk (conjY n w0Y) = QuotientGroup.mk w0Y
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have hcoe : ((conjY n w0Y : ↥Y) : G) = (n : G) * w₀ * (n : G)⁻¹ :=
      conjAutHomOf_apply N Y hNY n w0Y
    rw [show ((conjY n w0Y / w0Y : ↥Y) : G) = ((conjY n w0Y : ↥Y) : G) * w₀⁻¹ from by
      rw [Subgroup.coe_div, div_eq_mul_inv], hcoe]
    exact hw₀fix (n : G) n.2 hG
  let aN : ↥N := ⟨a, haN⟩
  have hav0' : conjE aN v0' = z' * v0' := by
    apply Subtype.ext
    change a * v₀ * a⁻¹ = z * v₀
    exact hav₀
  have hcY_mem : ⁅a, w₀⁆ ∈ Y := by
    have hsplit : ⁅a, w₀⁆ = wz * (wz⁻¹ * ⁅a, w₀⁆) := by group
    rw [hsplit]
    exact Y.mul_mem hwzY (hQY haw₀)
  let cY : ↥Y := ⟨⁅a, w₀⁆, hcY_mem⟩
  have hqY : wzY⁻¹ * cY ∈ Qy := by
    rw [Subgroup.mem_subgroupOf]
    change wz⁻¹ * ⁅a, w₀⁆ ∈ Q
    exact haw₀
  have haw0' : actH aN w0' = w0' * wz' := by
    have hy1 : conjY aN w0Y = cY * w0Y := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      change (a : G) * w₀ * (a : G)⁻¹ = ⁅a, w₀⁆ * w₀
      rw [commutatorElement_def]
      group
    have hc_eq : QuotientGroup.mk' Qy cY = QuotientGroup.mk' Qy wzY := by
      have hprod : QuotientGroup.mk' Qy wzY⁻¹ * QuotientGroup.mk' Qy cY = 1 := by
        rw [← map_mul]
        exact (QuotientGroup.eq_one_iff (N := Qy) _).mpr hqY
      have h := (inv_eq_of_mul_eq_one_right hprod).symm
      rwa [map_inv, inv_inv] at h
    change QuotientGroup.mk' Qy (conjY aN w0Y) =
      QuotientGroup.mk' Qy w0Y * QuotientGroup.mk' Qy wzY
    rw [hy1, map_mul, hc_eq]
    exact hWcomm _ _
  obtain ⟨M', hM'inv, hM'inf, hM'sup, hwzM'⟩ :=
    ase_complement actH conjE pi hπ hπact hWexp hV8 hU
      (z := z') hz1' hzfix' htrans' hpairs'
      (wz := wz') hwzπ hwzfix'
      (v₀ := v0') hv01' hv0z' (w₀ := w0') hw0π hw0fix'
      (a := aN) hav0' haw0'
  let M : Subgroup G := (M'.comap (QuotientGroup.mk' Qy)).map Y.subtype
  have hQM : Q ≤ M := by
    intro q hq
    refine Subgroup.mem_map.mpr ⟨⟨q, hQY hq⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' Qy (⟨q, hQY hq⟩ : ↥Y) = 1 :=
      (QuotientGroup.eq_one_iff (N := Qy) (⟨q, hQY hq⟩ : ↥Y)).mpr
        (by rw [Subgroup.mem_subgroupOf]; exact hq)
    rw [h1]
    exact M'.one_mem
  have hMY : M ≤ Y := by
    intro m hm
    rcases Subgroup.mem_map.mp hm with ⟨y, _, rfl⟩
    exact y.2
  have hMinv : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M := by
    intro n hn m hm
    rcases Subgroup.mem_map.mp hm with ⟨y, hy, rfl⟩
    have hy' : QuotientGroup.mk' Qy y ∈ M' := Subgroup.mem_comap.mp hy
    refine Subgroup.mem_map.mpr ⟨conjY ⟨n, hn⟩ y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h2 : actH ⟨n, hn⟩ (QuotientGroup.mk' Qy y) =
        QuotientGroup.mk' Qy (conjY ⟨n, hn⟩ y) := rfl
    rw [← h2]
    exact hM'inv ⟨n, hn⟩ _ hy'
  have hMinf : M ⊓ X₀ = Q := by
    apply le_antisymm
    · intro m hm
      rcases Subgroup.mem_map.mp hm.1 with ⟨y, hy, hym⟩
      have hy' : QuotientGroup.mk' Qy y ∈ M' := Subgroup.mem_comap.mp hy
      have hyX : (y : G) ∈ X₀ := by
        have : (y : G) = m := hym
        rw [this]; exact hm.2
      have hpi : QuotientGroup.mk' Qy y ∈ pi.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext ((hφker (y : G) y.2).mpr hyX)
      have hthis : QuotientGroup.mk' Qy y ∈ M' ⊓ pi.ker := ⟨hy', hpi⟩
      rw [hM'inf] at hthis
      have hyQ : y ∈ Qy :=
        (QuotientGroup.eq_one_iff (N := Qy) y).mp (Subgroup.mem_bot.mp hthis)
      have hm_eq : m = (y : G) := hym.symm
      rw [hm_eq]
      exact Subgroup.mem_subgroupOf.mp hyQ
    · intro q hq
      exact ⟨hQM hq, hQX hq⟩
  have hMsup : M ⊔ X₀ = Y := by
    apply le_antisymm
    · exact sup_le hMY hXY
    · intro y hy
      let yY : ↥Y := ⟨y, hy⟩
      have hw : QuotientGroup.mk' Qy yY ∈ M' ⊔ pi.ker := by
        rw [hM'sup]; exact Subgroup.mem_top _
      have hw' : ∃ m' ∈ M', ∃ k ∈ pi.ker, m' * k = QuotientGroup.mk' Qy yY :=
        (Subgroup.mem_sup_of_normal_right (s := M') (t := pi.ker)
          (x := QuotientGroup.mk' Qy yY)).mp hw
      rcases hw' with ⟨m', hm', k, hk, hmk⟩
      obtain ⟨z₁, rfl⟩ := QuotientGroup.mk'_surjective Qy k
      obtain ⟨z', hz'mk⟩ := QuotientGroup.mk'_surjective Qy m'
      have hzX : (z₁ : G) ∈ X₀ := by
        have h1 : phiY z₁ = 1 := MonoidHom.mem_ker.mp hk
        exact (hφker (z₁ : G) z₁.2).mp (Subtype.ext_iff.mp h1)
      have hzM : (z' : G) ∈ M := by
        refine Subgroup.mem_map.mpr ⟨z', ?_, rfl⟩
        rw [Subgroup.mem_comap, hz'mk]
        exact hm'
      have heq : QuotientGroup.mk' Qy (z' * z₁) = QuotientGroup.mk' Qy yY := by
        rw [map_mul, hz'mk, hmk]
      have hydiv : yY / (z' * z₁) ∈ Qy := by
        rw [← QuotientGroup.eq_iff_div_mem]
        exact heq.symm
      have hfQ : ((yY / (z' * z₁) : ↥Y) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hydiv
      have hy_eq : y = ((yY / (z' * z₁) : ↥Y) : G) * ((z' * z₁ : ↥Y) : G) := by
        change (yY : G) = ((yY / (z' * z₁) : ↥Y) : G) * ((z' * z₁ : ↥Y) : G)
        rw [Subgroup.coe_div, Subgroup.coe_mul, div_eq_mul_inv]
        group
      rw [hy_eq]
      exact (M ⊔ X₀).mul_mem (Subgroup.mem_sup_left (hQM hfQ))
        ((M ⊔ X₀).mul_mem (Subgroup.mem_sup_left hzM) (Subgroup.mem_sup_right hzX))
  have hwzM : wz ∈ M := by
    refine Subgroup.mem_map.mpr ⟨wzY, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hwzM'
  exact ⟨M, hQM, hMY, hMinv, hMinf, hMsup, hwzM⟩

end CFSG.OddStandard.HigherRank.YamadaG23
