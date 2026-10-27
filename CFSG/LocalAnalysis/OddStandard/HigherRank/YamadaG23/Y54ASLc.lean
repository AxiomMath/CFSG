module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54ASLb

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

theorem asl_split_sub {F X₀ Y N S : Subgroup G} (φ : G → G) (hFX : F ≤ X₀) (hXY : X₀ ≤ Y)
    (hFn : ∀ y ∈ Y, ∀ f ∈ F, y * f * y⁻¹ ∈ F) (hsq : ∀ y ∈ Y, y ^ 2 ∈ F)
    (hNY : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) (hNF : ∀ n ∈ N, ∀ f ∈ F, n * f * n⁻¹ ∈ F)
    (hNX : ∀ n ∈ N, ∀ x ∈ X₀, ⁅n, x⁆ ∈ F)
    (hφmul : ∀ y ∈ Y, ∀ y' ∈ Y, φ (y * y') = φ y * φ y') (hφmem : ∀ y ∈ Y, φ y ∈ F)
    (hφker : ∀ y ∈ Y, (φ y = 1 ↔ y ∈ X₀)) (hφsurj : ∀ f ∈ F, ∃ y ∈ Y, φ y = f)
    (hφconj : ∀ n ∈ N, ∀ y ∈ Y, φ (n * y * n⁻¹) = n * φ y * n⁻¹)
    (hF : IsE 3 ↥F)
    (htrans : ∀ a ∈ F, ∀ b ∈ F, ∀ a' ∈ F, ∀ b' ∈ F, a ≠ 1 → b ≠ 1 → a ≠ b → a' ≠ 1 → b' ≠ 1 →
      a' ≠ b' → ∃ n ∈ N, n * a * n⁻¹ = a' ∧ n * b * n⁻¹ = b')
    (hSN : S ≤ N) (hidx : Nat.card ↥N = 21 * Nat.card ↥S)
    {w₀ : G} (hw₀Y : w₀ ∈ Y) (hw₀φ : φ w₀ ≠ 1) (hw₀S : ∀ x ∈ S, ⁅x, w₀⁆ ∈ F) :
    ∃ M : Subgroup G, F ≤ M ∧ M ≤ Y ∧ (∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) ∧ M ⊓ X₀ = F ∧
      M ⊔ X₀ = Y := by
  have hFY : F ≤ Y := hFX.trans hXY
  let Fy : Subgroup ↥Y := F.subgroupOf Y
  haveI : Fy.Normal :=
    (Subgroup.normal_subgroupOf_iff hFY).mpr fun h k hh hk => hFn k hk h hh
  let conjY : ↥N →* MulAut ↥Y := conjAutHomOf N Y hNY
  let conjF : ↥N →* MulAut ↥F := conjAutHomOf N F hNF
  have he (n : ↥N) : Fy.map (conjY n : ↥Y →* ↥Y) = Fy := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      exact hNF n n.2 a ha
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨(conjY n)⁻¹ x, ?_, MulEquiv.apply_symm_apply (conjY n) x⟩
      rw [← map_inv conjY n]
      exact hNF _ (N.inv_mem n.2) x hx
  let actH : ↥N →* MulAut (↥Y ⧸ Fy) :=
    { toFun n := QuotientGroup.congr Fy Fy (conjY n) (he n)
      map_one' := by
        ext w
        induction w using QuotientGroup.induction_on with
        | H y =>
          change (((conjY 1 : MulAut ↥Y) y : ↥Y) : ↥Y ⧸ Fy) = (y : ↥Y ⧸ Fy)
          rw [map_one]
          rfl
      map_mul' n m := by
        ext w
        induction w using QuotientGroup.induction_on with
        | H y =>
          change (((conjY (n * m) : MulAut ↥Y) y : ↥Y) : ↥Y ⧸ Fy) =
            (((conjY n : MulAut ↥Y) ((conjY m : MulAut ↥Y) y) : ↥Y) : ↥Y ⧸ Fy)
          rw [map_mul, MulAut.mul_apply] }
  let phiY : ↥Y →* ↥F :=
    { toFun y := ⟨φ (y : G), hφmem (y : G) y.2⟩
      map_one' := Subtype.ext ((hφker (1 : G) Y.one_mem).mpr X₀.one_mem)
      map_mul' y y' := Subtype.ext (hφmul (y : G) y.2 (y' : G) y'.2) }
  have hker : Fy ≤ phiY.ker := by
    intro f hf
    rw [MonoidHom.mem_ker]
    exact Subtype.ext ((hφker (f : G) f.2).mpr (hFX (Subgroup.mem_subgroupOf.mp hf)))
  let pi : (↥Y ⧸ Fy) →* ↥F := QuotientGroup.lift Fy phiY hker
  have hπ : Function.Surjective pi := by
    intro f
    obtain ⟨y, hy, hφy⟩ := hφsurj (f : G) f.2
    exact ⟨QuotientGroup.mk' Fy ⟨y, hy⟩, Subtype.ext hφy⟩
  have hπact : ∀ (n : ↥N) (w : ↥Y ⧸ Fy), pi (actH n w) = conjF n (pi w) := by
    intro n w
    induction w using QuotientGroup.induction_on with
    | H y =>
      change phiY (conjY n y) = conjF n (phiY y)
      exact Subtype.ext (hφconj (n : G) n.2 (y : G) y.2)
  have hW : ∀ w : ↥Y ⧸ Fy, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H y =>
      rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [pow_two] using hsq (y : G) y.2
  have hV8 : Nat.card ↥F = 8 := by
    rw [hF.2]; norm_num
  have hU : ∀ (n : ↥N) (u : ↥Y ⧸ Fy), u ∈ pi.ker → actH n u = u := by
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
  have htrans' : ∀ a b a' b' : ↥F, a ≠ 1 → b ≠ 1 → a ≠ b → a' ≠ 1 → b' ≠ 1 → a' ≠ b' →
      ∃ n : ↥N, conjF n a = a' ∧ conjF n b = b' := by
    intro a b a' b' ha hb hab ha' hb' hab'
    obtain ⟨n, hnN, hna, hnb⟩ := htrans (a : G) a.2 (b : G) b.2 (a' : G) a'.2 (b' : G) b'.2
      (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
      (fun h => hab (Subtype.ext h)) (fun h => ha' (Subtype.ext h))
      (fun h => hb' (Subtype.ext h)) (fun h => hab' (Subtype.ext h))
    exact ⟨⟨n, hnN⟩, Subtype.ext hna, Subtype.ext hnb⟩
  let S' : Subgroup ↥N := S.subgroupOf N
  have hidx' : Nat.card ↥N = 21 * Nat.card ↥S' := by
    have hcard : Nat.card ↥S' = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
    rw [hidx, hcard]
  let w' : ↥Y ⧸ Fy := QuotientGroup.mk (⟨w₀, hw₀Y⟩ : ↥Y)
  have hw₀' : ∀ x ∈ S', actH x w' = w' := by
    intro x hx
    have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    change QuotientGroup.mk (conjY x ⟨w₀, hw₀Y⟩) = QuotientGroup.mk (⟨w₀, hw₀Y⟩ : ↥Y)
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have hcoe : ((conjY x ⟨w₀, hw₀Y⟩ : ↥Y) : G) = (x : G) * w₀ * (x : G)⁻¹ :=
      conjAutHomOf_apply N Y hNY x ⟨w₀, hw₀Y⟩
    rw [show ((conjY x ⟨w₀, hw₀Y⟩ / ⟨w₀, hw₀Y⟩ : ↥Y) : G) =
        ((conjY x ⟨w₀, hw₀Y⟩ : ↥Y) : G) * w₀⁻¹ from by
      rw [Subgroup.coe_div, div_eq_mul_inv], hcoe]
    exact hw₀S (x : G) hxS
  have hw₀1' : pi w' ≠ 1 := by
    intro h
    apply hw₀φ
    have h1 : phiY ⟨w₀, hw₀Y⟩ = 1 := h
    exact Subtype.ext_iff.mp h1
  obtain ⟨M', hM'inv, hM'inf, hM'sup⟩ :=
    asl_complement actH conjF pi hπ hπact hW hV8 hU htrans' S' hidx' hw₀' hw₀1'
  let M : Subgroup G := (M'.comap (QuotientGroup.mk' Fy)).map Y.subtype
  have hFM : F ≤ M := by
    intro f hf
    refine Subgroup.mem_map.mpr ⟨⟨f, hFY hf⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' Fy (⟨f, hFY hf⟩ : ↥Y) = 1 :=
      (QuotientGroup.eq_one_iff (N := Fy) (⟨f, hFY hf⟩ : ↥Y)).mpr
        (by rw [Subgroup.mem_subgroupOf]; exact hf)
    rw [h1]
    exact M'.one_mem
  have hMY : M ≤ Y := by
    intro m hm
    rcases Subgroup.mem_map.mp hm with ⟨y, _, rfl⟩
    exact y.2
  have hMinv : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M := by
    intro n hn m hm
    rcases Subgroup.mem_map.mp hm with ⟨y, hy, rfl⟩
    have hy' : QuotientGroup.mk' Fy y ∈ M' := Subgroup.mem_comap.mp hy
    refine Subgroup.mem_map.mpr ⟨conjY ⟨n, hn⟩ y, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h2 : actH ⟨n, hn⟩ (QuotientGroup.mk' Fy y) = QuotientGroup.mk' Fy (conjY ⟨n, hn⟩ y) :=
      rfl
    rw [← h2]
    exact hM'inv ⟨n, hn⟩ _ hy'
  have hMinf : M ⊓ X₀ = F := by
    apply le_antisymm
    · intro m hm
      rcases Subgroup.mem_map.mp hm.1 with ⟨y, hy, hym⟩
      have hy' : QuotientGroup.mk' Fy y ∈ M' := Subgroup.mem_comap.mp hy
      have hyX : (y : G) ∈ X₀ := by
        have : (y : G) = m := hym
        rw [this]; exact hm.2
      have hpi : QuotientGroup.mk' Fy y ∈ pi.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext ((hφker (y : G) y.2).mpr hyX)
      have hthis : QuotientGroup.mk' Fy y ∈ M' ⊓ pi.ker := ⟨hy', hpi⟩
      rw [hM'inf] at hthis
      have hyF : y ∈ Fy :=
        (QuotientGroup.eq_one_iff (N := Fy) y).mp (Subgroup.mem_bot.mp hthis)
      have hm_eq : m = (y : G) := hym.symm
      rw [hm_eq]
      exact Subgroup.mem_subgroupOf.mp hyF
    · intro f hf
      exact ⟨hFM hf, hFX hf⟩
  have hMsup : M ⊔ X₀ = Y := by
    apply le_antisymm
    · exact sup_le hMY hXY
    · intro y hy
      let yY : ↥Y := ⟨y, hy⟩
      have hw : QuotientGroup.mk' Fy yY ∈ M' ⊔ pi.ker := by
        rw [hM'sup]; exact Subgroup.mem_top _
      have hw' : ∃ m' ∈ M', ∃ k ∈ pi.ker, m' * k = QuotientGroup.mk' Fy yY :=
        (Subgroup.mem_sup_of_normal_right (s := M') (t := pi.ker)
          (x := QuotientGroup.mk' Fy yY)).mp hw
      rcases hw' with ⟨m', hm', k, hk, hmk⟩
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Fy k
      obtain ⟨z', hz'mk⟩ := QuotientGroup.mk'_surjective Fy m'
      have hzX : (z : G) ∈ X₀ := by
        have h1 : phiY z = 1 := MonoidHom.mem_ker.mp hk
        exact (hφker (z : G) z.2).mp (Subtype.ext_iff.mp h1)
      have hzM : (z' : G) ∈ M := by
        refine Subgroup.mem_map.mpr ⟨z', ?_, rfl⟩
        rw [Subgroup.mem_comap, hz'mk]
        exact hm'
      have heq : QuotientGroup.mk' Fy (z' * z) = QuotientGroup.mk' Fy yY := by
        rw [map_mul, hz'mk, hmk]
      have hydiv : yY / (z' * z) ∈ Fy := by
        rw [← QuotientGroup.eq_iff_div_mem]
        exact heq.symm
      have hfF : ((yY / (z' * z) : ↥Y) : G) ∈ F := Subgroup.mem_subgroupOf.mp hydiv
      have hy_eq : y = ((yY / (z' * z) : ↥Y) : G) * ((z' * z : ↥Y) : G) := by
        change (yY : G) = ((yY / (z' * z) : ↥Y) : G) * ((z' * z : ↥Y) : G)
        rw [Subgroup.coe_div, Subgroup.coe_mul, div_eq_mul_inv]
        group
      rw [hy_eq]
      exact (M ⊔ X₀).mul_mem (Subgroup.mem_sup_left (hFM hfF))
        ((M ⊔ X₀).mul_mem (Subgroup.mem_sup_left hzM) (Subgroup.mem_sup_right hzX))
  exact ⟨M, hFM, hMY, hMinv, hMinf, hMsup⟩

end CFSG.OddStandard.HigherRank.YamadaG23
