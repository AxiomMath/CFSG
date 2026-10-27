module

public import CFSG.GF2Type.Smith1980Orth.TwoRankSmallData
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Arf
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

namespace TwoRankSmall

open CFSG.Open

structure Coding (W : Type) [AddCommGroup W] (N : ℕ) where
  e : W ≃ Fin N
  e_add : ∀ v w, (e (v + w)).val = (e v).val ^^^ (e w).val

private theorem foldr_range (N : ℕ) (G : ℕ → ℕ) (n : ℕ) :
    ∀ a, (List.range n).foldr (fun x acc => G x + N * acc) a =
      (∑ i ∈ Finset.range n, G i * N ^ i) + N ^ n * a := by
  induction n with
  | zero =>
    intro a
    simp
  | succ n ih =>
    intro a
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih,
      Finset.sum_range_succ, pow_succ]
    ring

namespace Coding

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {N : ℕ} (c : Coding W N)

def code (g : W ≃ₗ[ZMod 2] W) : Fin N → Fin N := fun x => c.e (g (c.e.symm x))

def pk (g : W ≃ₗ[ZMod 2] W) : ℕ := (finFunctionFinEquiv (c.code g)).val

private theorem code_mul (g h : W ≃ₗ[ZMod 2] W) (x : Fin N) :
    c.code (g * h) x = c.code g (c.code h x) := by
  simp [code, LinearEquiv.mul_apply]

private theorem code_one (x : Fin N) : c.code (1 : W ≃ₗ[ZMod 2] W) x = x := by
  simp [code]

private theorem getN_pk (g : W ≃ₗ[ZMod 2] W) (x : Fin N) :
    getN N (c.pk g) x = (c.code g x).val := by
  have h : ((finFunctionFinEquiv.symm (finFunctionFinEquiv (c.code g))) x).val =
      (c.code g x).val := by
    rw [Equiv.symm_apply_apply]
  rw [finFunctionFinEquiv_symm_apply_val] at h
  exact h

private theorem e_apply (g : W ≃ₗ[ZMod 2] W) (v : W) :
    (c.e (g v)).val = getN N (c.pk g) (c.e v).val := by
  have h := c.getN_pk g (c.e v)
  simpa [code] using h.symm

private theorem pk_mul (g h : W ≃ₗ[ZMod 2] W) : c.pk (g * h) = compN N (c.pk g) (c.pk h) := by
  unfold compN
  rw [foldr_range N (fun x => getN N (c.pk g) (getN N (c.pk h) x)) N 0, mul_zero, add_zero,
    Finset.sum_range]
  have hL : c.pk (g * h) = ∑ i : Fin N, (c.code (g * h) i).val * N ^ i.val := by
    simp [pk, finFunctionFinEquiv_apply_val]
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [c.getN_pk h i, c.getN_pk g (c.code h i), c.code_mul]

private theorem pk_one : c.pk (1 : W ≃ₗ[ZMod 2] W) = idN N := by
  unfold idN
  rw [foldr_range N (fun x => x) N 0, mul_zero, add_zero, Finset.sum_range]
  simp [pk, finFunctionFinEquiv_apply_val, code_one]

private theorem pk_injective : Function.Injective (c.pk : (W ≃ₗ[ZMod 2] W) → ℕ) := by
  intro g h hgh
  have h1 : c.code g = c.code h := finFunctionFinEquiv.injective (Fin.ext hgh)
  ext v
  have h2 := congrFun h1 (c.e v)
  simp only [code, Equiv.symm_apply_apply] at h2
  exact c.e.injective h2

private theorem exists_pk_eq [Finite W] {t : ℕ} (ht : t < N ^ N)
    (hadd : ∀ x < N, ∀ y < N, getN N t (x ^^^ y) = getN N t x ^^^ getN N t y)
    (hinj : ∀ x < N, ∀ y < N, getN N t x = getN N t y → x = y) :
    ∃ g : W ≃ₗ[ZMod 2] W, c.pk g = t := by
  let sF : Fin N → Fin N := finFunctionFinEquiv.symm ⟨t, ht⟩
  have hsF : ∀ x : Fin N, (sF x).val = getN N t x := fun x => by simp [sF, getN]
  let f : W → W := fun v => c.e.symm (sF (c.e v))
  have hf : ∀ v, (c.e (f v)).val = getN N t (c.e v).val := fun v => by
    simp [f, hsF]
  have hfadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    apply c.e.injective
    apply Fin.ext
    calc (c.e (f (v + w))).val = getN N t (c.e (v + w)).val := hf _
      _ = getN N t ((c.e v).val ^^^ (c.e w).val) := by rw [c.e_add]
      _ = getN N t (c.e v).val ^^^ getN N t (c.e w).val := hadd _ (c.e v).isLt _ (c.e w).isLt
      _ = (c.e (f v)).val ^^^ (c.e (f w)).val := by rw [hf, hf]
      _ = (c.e (f v + f w)).val := (c.e_add _ _).symm
  have hfinj : Function.Injective f := by
    intro v w h
    have h1 := congrArg (fun u => (c.e u).val) h
    simp only [hf] at h1
    exact c.e.injective (Fin.ext (hinj _ (c.e v).isLt _ (c.e w).isLt h1))
  let F : W →ₗ[ZMod 2] W := (AddMonoidHom.mk' f hfadd).toZModLinearMap 2
  have hFb : Function.Bijective F := ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  let g : W ≃ₗ[ZMod 2] W := LinearEquiv.ofBijective F hFb
  refine ⟨g, ?_⟩
  have hcode : c.code g = sF := by
    funext x
    simp [code, g, F, f]
  rw [pk, hcode]
  simp [sF]

private theorem mem_isometries {q : W → ZMod 2} {qt : ℕ}
    (hqt : ∀ v, q v = ((getN 2 qt (c.e v).val : ℕ) : ZMod 2)) {g : W ≃ₗ[ZMod 2] W} {t : ℕ}
    (hg : c.pk g = t) (hiso : ∀ x < N, getN 2 qt (getN N t x) = getN 2 qt x) :
    g ∈ timmesfeldIsometries q := by
  show ∀ v, q (g v) = q v
  intro v
  rw [hqt (g v), hqt v, c.e_apply g v, hg, hiso _ (c.e v).isLt]

end Coding

section Sylow

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {N : ℕ} (c : Coding W N)

private theorem card_le_of_color [Finite W] {r cls : ℕ} {P : List ℕ}
    (hC₁ : ColorOK₁ N (2 ^ (r + 1) - 2) cls P) (hC₂ : ColorOK₂ N (2 ^ (r + 1) - 2) cls P)
    {F : Subgroup (W ≃ₗ[ZMod 2] W)} (hF : ∀ g ∈ F, c.pk g ∈ P) (h2 : ∀ x ∈ F, x * x = 1) :
    Nat.card F ≤ 2 ^ r := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun g : W ≃ₗ[ZMod 2] W => (g : W → W)) DFunLike.coe_injective
  haveI : Fintype F := Fintype.ofFinite F
  have hp : IsPGroup 2 F := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h2 x.1 x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hrk : r + 1 ≤ k := by
    rw [hk] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have hbig : 2 ^ (r + 1) ≤ Nat.card F := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hrk
  have hcomm : ∀ x y : F, x * y = y * x := by
    intro x y
    have hx := h2 x.1 x.2
    have hy := h2 y.1 y.2
    have hxy := h2 (x.1 * y.1) (F.mul_mem x.2 y.2)
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    have h3 : x.1 * y.1 = (x.1 * y.1)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    rw [h3, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  have hpos : ∀ x : F, ∃ i, i < P.length ∧ P.getD i 0 = c.pk x.1 := by
    intro x
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 (hF _ x.2)
    refine ⟨i, hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simpa using hix
  choose idx hidx hidxe using hpos
  have hinv : ∀ x : F, x ≠ 1 → isInvN N (P.getD (idx x) 0) = true := by
    intro x hx
    rw [hidxe]
    have e1 : compN N (c.pk x.1) (c.pk x.1) = idN N := by
      rw [← c.pk_mul, h2 x.1 x.2, c.pk_one]
    have e2 : c.pk x.1 ≠ idN N := by
      intro h
      apply hx
      apply Subtype.ext
      apply c.pk_injective
      rw [h, ← c.pk_one]
      rfl
    simp [isInvN, e1, e2]
  have hcol : ∀ x : F, x ≠ 1 → getN 64 cls (idx x) < 2 ^ (r + 1) - 2 :=
    fun x hx => hC₁ _ (hidx x) (hinv x hx)
  set S : Finset F := (Finset.univ : Finset F).erase 1 with hS
  have hSc : S.card = Nat.card F - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hinj : Set.InjOn (fun x : F => getN 64 cls (idx x)) (S : Set F) := by
    intro x hx y hy hxy
    have hx1 : x ≠ 1 := (Finset.mem_erase.1 (Finset.mem_coe.1 hx)).1
    by_contra hne
    have hij : idx x ≠ idx y := by
      intro h
      apply hne
      apply Subtype.ext
      apply c.pk_injective
      rw [← hidxe x, ← hidxe y, h]
    apply hC₂ (idx x) (hidx x) (hcol x hx1) (idx y) (hidx y) hij hxy
    rw [hidxe, hidxe, ← c.pk_mul, ← c.pk_mul]
    exact congrArg c.pk (congrArg Subtype.val (hcomm x y))
  have hcard : S.card ≤ (Finset.range (2 ^ (r + 1) - 2)).card := by
    apply Finset.card_le_card_of_injOn (fun x : F => getN 64 cls (idx x)) _ hinj
    intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_coe, Finset.mem_range]
    exact hcol x (Finset.mem_erase.1 hx).1
  rw [Finset.card_range] at hcard
  have hpos : 0 < 2 ^ r := by positivity
  omega

theorem card_le_of_cert [Finite W] {q : W → ZMod 2} {qt : ℕ}
    (hqt : ∀ v, q v = ((getN 2 qt (c.e v).val : ℕ) : ZMod 2)) {a r cls succ : ℕ}
    {gens P : List ℕ} {info : List (ℕ × ℕ)} (hP : TabCert N a r qt cls succ gens P info)
    {m : ℕ} (hm : Odd m) (hord : Nat.card (timmesfeldIsometries q) = 2 ^ a * m)
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hE : E ≤ timmesfeldIsometries q)
    (h2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun g : W ≃ₗ[ZMod 2] W => (g : W → W)) DFunLike.coe_injective
  obtain ⟨hGens, hTree, hIso, hC₁, hC₂⟩ := hP
  obtain ⟨hP0, hPnd, hPlen, hlen, hinfo, hsucc⟩ := hTree
  have hgen : ∀ j : Fin gens.length, ∃ g : W ≃ₗ[ZMod 2] W,
      c.pk g = gens.getD j 0 ∧ g ∈ timmesfeldIsometries q := by
    intro j
    have hmem : gens.getD j 0 ∈ gens := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.2]
      exact List.getElem_mem j.2
    obtain ⟨hlt, hadd, hnd⟩ := hGens _ hmem
    have hadd' : ∀ x < N, ∀ y < N, getN N (gens.getD j 0) (x ^^^ y) =
        getN N (gens.getD j 0) x ^^^ getN N (gens.getD j 0) y := by
      intro x hx y hy
      rcases le_total x y with h | h
      · exact hadd x hx y hy h
      · rw [Nat.xor_comm x y, Nat.xor_comm (getN N (gens.getD j 0) x)]
        exact hadd y hy x hx h
    have hinj : ∀ x < N, ∀ y < N, getN N (gens.getD j 0) x = getN N (gens.getD j 0) y → x = y :=
      fun x hx y hy h =>
        List.inj_on_of_nodup_map hnd (List.mem_range.2 hx) (List.mem_range.2 hy) h
    obtain ⟨g, hg⟩ := c.exists_pk_eq hlt hadd' hinj
    exact ⟨g, hg, c.mem_isometries hqt hg (hIso _ hmem)⟩
  choose gA hgA using hgen
  have hmemP : ∀ n, n < P.length → P.getD n 0 ∈ P := by
    intro n hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    exact List.getElem_mem hn
  have hposP : ∀ s ∈ P, ∃ n, n < P.length ∧ P.getD n 0 = s := by
    intro s hs
    obtain ⟨n, hn, hns⟩ := List.mem_iff_getElem.1 hs
    refine ⟨n, hn, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    simpa using hns
  have hPpos : 0 < P.length := by
    rw [hPlen]
    positivity
  have hQ : ∀ i, i < P.length →
      (∃ w : W ≃ₗ[ZMod 2] W, w ∈ timmesfeldIsometries q ∧ c.pk w = P.getD i 0) ∧
      ∀ x y : W ≃ₗ[ZMod 2] W, c.pk x ∈ P → c.pk y = P.getD i 0 → c.pk (x * y) ∈ P := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have h0 : c.pk (1 : W ≃ₗ[ZMod 2] W) = P.getD 0 0 := by rw [c.pk_one, hP0]
        refine ⟨⟨1, one_mem _, h0⟩, fun x y hx hy => ?_⟩
        have : y = 1 := c.pk_injective (hy.trans h0.symm)
        rw [this, mul_one]
        exact hx
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k < info.length := by omega
        obtain ⟨hp, hj, hs⟩ := hinfo k hk
        have hedge := (hsucc (info.getD k (0, 0)).1 (by omega) (info.getD k (0, 0)).2 hj).2
        rw [hs] at hedge
        obtain ⟨⟨wp, hwpG, hwp⟩, hclp⟩ := ih (info.getD k (0, 0)).1 (by omega) (by omega)
        have hgpk : c.pk (gA ⟨(info.getD k (0, 0)).2, hj⟩) = gens.getD (info.getD k (0, 0)).2 0 :=
          (hgA ⟨(info.getD k (0, 0)).2, hj⟩).1
        have hgG : gA ⟨(info.getD k (0, 0)).2, hj⟩ ∈ timmesfeldIsometries q :=
          (hgA ⟨(info.getD k (0, 0)).2, hj⟩).2
        have hpkw : c.pk (wp * gA ⟨(info.getD k (0, 0)).2, hj⟩) = P.getD (k + 1) 0 := by
          rw [c.pk_mul, hwp, hgpk]
          exact hedge
        refine ⟨⟨wp * gA ⟨(info.getD k (0, 0)).2, hj⟩, mul_mem hwpG hgG, hpkw⟩,
          fun x y hx hy => ?_⟩
        have hy' : y = wp * gA ⟨(info.getD k (0, 0)).2, hj⟩ :=
          c.pk_injective (hy.trans hpkw.symm)
        rw [hy', ← mul_assoc]
        obtain ⟨i', hi', hi'e⟩ := hposP _ (hclp x wp hx hwp)
        rw [c.pk_mul, hgpk, ← hi'e]
        have h3 := hsucc i' hi' (info.getD k (0, 0)).2 hj
        rw [h3.2]
        exact hmemP _ h3.1
  have hmul : ∀ x y : W ≃ₗ[ZMod 2] W, c.pk x ∈ P → c.pk y ∈ P → c.pk (x * y) ∈ P := by
    intro x y hx hy
    obtain ⟨i, hi, hiy⟩ := hposP _ hy
    exact (hQ i hi).2 x y hx hiy.symm
  have h1P : c.pk (1 : W ≃ₗ[ZMod 2] W) ∈ P := by
    rw [c.pk_one, ← hP0]
    exact hmemP 0 hPpos
  have hpow : ∀ x : W ≃ₗ[ZMod 2] W, c.pk x ∈ P → ∀ n : ℕ, c.pk (x ^ n) ∈ P := by
    intro x hx n
    induction n with
    | zero =>
      rw [pow_zero]
      exact h1P
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ _ ih hx
  have hinvP : ∀ x : W ≃ₗ[ZMod 2] W, c.pk x ∈ P → c.pk x⁻¹ ∈ P := by
    intro x hx
    have h1 : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    have h2 : x ^ (orderOf x - 1) = x⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [← h2]
    exact hpow x hx _
  let S : Subgroup (W ≃ₗ[ZMod 2] W) :=
    { carrier := {g | c.pk g ∈ P}
      mul_mem' := fun {x y} hx hy => hmul x y hx hy
      one_mem' := h1P
      inv_mem' := fun {x} hx => hinvP x hx }
  have hSmem : ∀ g, g ∈ S ↔ c.pk g ∈ P := fun g => Iff.rfl
  have hSG : S ≤ timmesfeldIsometries q := by
    intro g hg
    obtain ⟨i, hi, hie⟩ := hposP _ ((hSmem g).1 hg)
    obtain ⟨⟨w, hwG, hw⟩, -⟩ := hQ i hi
    have : g = w := c.pk_injective (hie.symm.trans hw.symm)
    rw [this]
    exact hwG
  have hScard : Nat.card S = 2 ^ a := by
    have hbij : Function.Bijective (fun g : S => (⟨c.pk g.1, g.2⟩ : {s // s ∈ P})) := by
      constructor
      · intro g₁ g₂ h
        exact Subtype.ext (c.pk_injective (congrArg Subtype.val h))
      · rintro ⟨s, hs⟩
        obtain ⟨i, hi, hie⟩ := hposP s hs
        obtain ⟨⟨w, -, hw⟩, -⟩ := hQ i hi
        exact ⟨⟨w, (hSmem w).2 (by rw [hw, hie]; exact hs)⟩, Subtype.ext (hw.trans hie)⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), ← hPlen, ← List.toFinset_card_of_nodup hPnd,
      ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun s => by simp)
  set G := timmesfeldIsometries q with hG
  have hv : (Nat.card G).factorization 2 = a := by
    have hm' : ¬ 2 ∣ m := by
      have := Nat.odd_iff.1 hm
      omega
    rw [hord, Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm', add_zero]
  have hSsub : Nat.card (S.subgroupOf G) = 2 ^ (Nat.card G).factorization 2 := by
    rw [hv, ← hScard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h2 x.1 x.2)⟩
  have hEp : IsPGroup 2 (E.subgroupOf G) := hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard _ hSsub)
  have hQ' : ((g • Q : Sylow 2 G) : Subgroup G) =
      (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hconj : (E.subgroupOf G).map (MulAut.conj g).toMonoidHom ≤ S.subgroupOf G := by
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hEQ
    rw [← hQ', hg] at this
    exact this
  let φ : G →* (W ≃ₗ[ZMod 2] W) := G.subtype.comp (MulAut.conj g).toMonoidHom
  have hφ : Function.Injective φ := (Subgroup.subtype_injective G).comp (MulAut.conj g).injective
  let F : Subgroup (W ≃ₗ[ZMod 2] W) := (E.subgroupOf G).map φ
  have hFS : ∀ x ∈ F, c.pk x ∈ P := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hconj (Subgroup.mem_map_of_mem _ hy)
    exact h1
  have hF2 : ∀ x ∈ F, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (by simpa using h2 y.1 hy)
    rw [this, map_one]
  have hFcard : Nat.card F = Nat.card E := by
    rw [Subgroup.card_map_of_injective hφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  rw [← hFcard]
  exact card_le_of_color c hC₁ hC₂ hFS hF2

end Sylow

theorem card_le_of_isometry {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W]
    [Module (ZMod 2) W] {q : V → ZMod 2} {r : W → ZMod 2} (φ : V ≃ₗ[ZMod 2] W)
    (hφ : ∀ v, r (φ v) = q v) {B : ℕ}
    (hB : ∀ F : Subgroup (W ≃ₗ[ZMod 2] W), F ≤ timmesfeldIsometries r →
      (∀ x ∈ F, x * x = 1) → Nat.card F ≤ B)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : E ≤ timmesfeldIsometries q)
    (h2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ B := by
  let ψ : (V ≃ₗ[ZMod 2] V) →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun g => φ.symm.trans (g.trans φ)
      map_one' := by
        ext
        simp
      map_mul' := fun g h => by
        ext
        simp }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    ext v
    have := LinearEquiv.congr_fun hgh (φ v)
    simpa [ψ] using this
  have key := hB (E.map ψ) ?_ ?_
  · rwa [Subgroup.card_map_of_injective hψ] at key
  · rintro _ ⟨g, hg, rfl⟩
    show ∀ w, r (φ (g (φ.symm w))) = r w
    intro w
    rw [hφ, hE hg (φ.symm w), ← hφ, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, h2 g hg, map_one]

def codeEquiv {ι : Type} (n : ℕ) (ie : ι ≃ Fin n) : (ι → ZMod 2) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr ie (Equiv.refl (ZMod 2))).trans (finFunctionFinEquiv (m := 2) (n := n))

private theorem codeEquiv_add {ι : Type} (n : ℕ) (ie : ι ≃ Fin n)
    (h : ∀ x y : Fin (2 ^ n), (codeEquiv n ie ((codeEquiv n ie).symm x +
      (codeEquiv n ie).symm y)).val = x.val ^^^ y.val) (v w : ι → ZMod 2) :
    (codeEquiv n ie (v + w)).val = (codeEquiv n ie v).val ^^^ (codeEquiv n ie w).val := by
  simpa using h (codeEquiv n ie v) (codeEquiv n ie w)

def plusIe3 : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

def minusIe3 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 ≃ Fin 6 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def plusIe2 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

def minusIe2 : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 ≃ Fin 4 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def plusCoding3 : Coding (Fin 3 ⊕ Fin 3 → ZMod 2) 64 where
  e := codeEquiv 6 plusIe3
  e_add := codeEquiv_add 6 plusIe3 (by decide +kernel)

def minusCoding3 : Coding (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) 64 where
  e := codeEquiv 6 minusIe3
  e_add := codeEquiv_add 6 minusIe3 (by decide +kernel)

def plusCoding2 : Coding (Fin 2 ⊕ Fin 2 → ZMod 2) 16 where
  e := codeEquiv 4 plusIe2
  e_add := codeEquiv_add 4 plusIe2 (by decide +kernel)

def minusCoding2 : Coding (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) 16 where
  e := codeEquiv 4 minusIe2
  e_add := codeEquiv_add 4 minusIe2 (by decide +kernel)

open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadPlus_apply quadMinus_apply)

private theorem quadPlus3_eq (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    quadPlus 3 (ZMod 2) v = ((getN 2 (qt6p ()) (plusCoding3.e v).val : ℕ) : ZMod 2) := by
  rw [quadPlus_apply]
  obtain ⟨x, rfl⟩ := plusCoding3.e.symm.surjective v
  have h : ∀ x : Fin 64, ∑ i : Fin 3, (plusCoding3.e.symm x) (Sum.inl i) *
      (plusCoding3.e.symm x) (Sum.inr i) = ((getN 2 (qt6p ()) x.val : ℕ) : ZMod 2) := by
    decide +kernel
  simpa using h x

private theorem quadMinus3_eq (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) :
    quadMinus 3 (ZMod 2) 1 1 v = ((getN 2 (qt6m ()) (minusCoding3.e v).val : ℕ) : ZMod 2) := by
  rw [quadMinus_apply]
  obtain ⟨x, rfl⟩ := minusCoding3.e.symm.surjective v
  have h : ∀ x : Fin 64, ∑ i : Fin (3 - 1), (minusCoding3.e.symm x) (Sum.inl i) *
      (minusCoding3.e.symm x) (Sum.inr (Sum.inl i)) +
      (minusCoding3.e.symm x) (Sum.inr (Sum.inr 0)) ^ 2 +
      1 * (minusCoding3.e.symm x) (Sum.inr (Sum.inr 0)) *
        (minusCoding3.e.symm x) (Sum.inr (Sum.inr 1)) +
      1 * (minusCoding3.e.symm x) (Sum.inr (Sum.inr 1)) ^ 2 =
      ((getN 2 (qt6m ()) x.val : ℕ) : ZMod 2) := by
    decide +kernel
  simpa using h x

private theorem quadPlus2_eq (v : Fin 2 ⊕ Fin 2 → ZMod 2) :
    quadPlus 2 (ZMod 2) v = ((getN 2 (qt4p ()) (plusCoding2.e v).val : ℕ) : ZMod 2) := by
  rw [quadPlus_apply]
  obtain ⟨x, rfl⟩ := plusCoding2.e.symm.surjective v
  have h : ∀ x : Fin 16, ∑ i : Fin 2, (plusCoding2.e.symm x) (Sum.inl i) *
      (plusCoding2.e.symm x) (Sum.inr i) = ((getN 2 (qt4p ()) x.val : ℕ) : ZMod 2) := by
    decide +kernel
  simpa using h x

private theorem quadMinus2_eq (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) :
    quadMinus 2 (ZMod 2) 1 1 v = ((getN 2 (qt4m ()) (minusCoding2.e v).val : ℕ) : ZMod 2) := by
  rw [quadMinus_apply]
  obtain ⟨x, rfl⟩ := minusCoding2.e.symm.surjective v
  have h : ∀ x : Fin 16, ∑ i : Fin (2 - 1), (minusCoding2.e.symm x) (Sum.inl i) *
      (minusCoding2.e.symm x) (Sum.inr (Sum.inl i)) +
      (minusCoding2.e.symm x) (Sum.inr (Sum.inr 0)) ^ 2 +
      1 * (minusCoding2.e.symm x) (Sum.inr (Sum.inr 0)) *
        (minusCoding2.e.symm x) (Sum.inr (Sum.inr 1)) +
      1 * (minusCoding2.e.symm x) (Sum.inr (Sum.inr 1)) ^ 2 =
      ((getN 2 (qt4m ()) x.val : ℕ) : ZMod 2) := by
    decide +kernel
  simpa using h x

private theorem isometries_eq_orthogonalGroup {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) :
    timmesfeldIsometries Q = TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.ext fun g => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff (Q := Q) (f := g)).symm

private theorem card_isometries_plus3 :
    Nat.card (timmesfeldIsometries (quadPlus 3 (ZMod 2))) = 2 ^ 7 * 315 := by
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 (ZMod 2))) : ℤ) = _ :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := ZMod 2) 2).2
  rw [isometries_eq_orthogonalGroup]
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 (ZMod 2))) : ℤ) =
      ((2 ^ 7 * 315 : ℕ) : ℤ) := by
    rw [h, Nat.card_zmod]
    first | decide | norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast h2

private theorem card_isometries_minus3 :
    Nat.card (timmesfeldIsometries (quadMinus 3 (ZMod 2) 1 1)) = 2 ^ 7 * 405 := by
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 (ZMod 2) 1 1)) : ℤ) = _ :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) (b := 1) (c := 1) 2
      (by decide)).2
  rw [isometries_eq_orthogonalGroup]
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 (ZMod 2) 1 1)) : ℤ) =
      ((2 ^ 7 * 405 : ℕ) : ℤ) := by
    rw [h, Nat.card_zmod]
    first | decide | norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast h2

private theorem card_isometries_plus2 :
    Nat.card (timmesfeldIsometries (quadPlus 2 (ZMod 2))) = 2 ^ 3 * 9 := by
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 (ZMod 2))) : ℤ) = _ :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := ZMod 2) 1).2
  rw [isometries_eq_orthogonalGroup]
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 (ZMod 2))) : ℤ) =
      ((2 ^ 3 * 9 : ℕ) : ℤ) := by
    rw [h, Nat.card_zmod]
    first | decide | norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast h2

private theorem card_isometries_minus2 :
    Nat.card (timmesfeldIsometries (quadMinus 2 (ZMod 2) 1 1)) = 2 ^ 3 * 15 := by
  have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1)) : ℤ) = _ :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) (b := 1) (c := 1) 1
      (by decide)).2
  rw [isometries_eq_orthogonalGroup]
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 (ZMod 2) 1 1)) : ℤ) =
      ((2 ^ 3 * 15 : ℕ) : ℤ) := by
    rw [h, Nat.card_zmod]
    first | decide | norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast h2

private theorem core_plus3
    {F : Subgroup ((Fin 3 ⊕ Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 ⊕ Fin 3 → ZMod 2))}
    (hF : F ≤ timmesfeldIsometries (quadPlus 3 (ZMod 2))) (h2 : ∀ x ∈ F, x * x = 1) :
    Nat.card F ≤ 16 :=
  (card_le_of_cert plusCoding3 quadPlus3_eq cert6p (m := 315) (by decide)
    card_isometries_plus3 hF h2).trans (by norm_num)

private theorem core_minus3
    {F : Subgroup ((Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → ZMod 2))}
    (hF : F ≤ timmesfeldIsometries (quadMinus 3 (ZMod 2) 1 1)) (h2 : ∀ x ∈ F, x * x = 1) :
    Nat.card F ≤ 16 :=
  (card_le_of_cert minusCoding3 quadMinus3_eq cert6m (m := 405) (by decide)
    card_isometries_minus3 hF h2).trans (by norm_num)

private theorem core_plus2
    {F : Subgroup ((Fin 2 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 → ZMod 2))}
    (hF : F ≤ timmesfeldIsometries (quadPlus 2 (ZMod 2))) (h2 : ∀ x ∈ F, x * x = 1) :
    Nat.card F ≤ 4 :=
  (card_le_of_cert plusCoding2 quadPlus2_eq cert4p (m := 9) (by decide)
    card_isometries_plus2 hF h2).trans (by norm_num)

private theorem core_minus2
    {F : Subgroup ((Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2))}
    (hF : F ≤ timmesfeldIsometries (quadMinus 2 (ZMod 2) 1 1)) (h2 : ∀ x ∈ F, x * x = 1) :
    Nat.card F ≤ 4 :=
  (card_le_of_cert minusCoding2 quadMinus2_eq cert4m (m := 15) (by decide)
    card_isometries_minus2 hF h2).trans (by norm_num)

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration in
private theorem exists_std_of_nondegenerate {n : ℕ}
    {q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)} (hq : timmesfeldNondegenerate q) :
    ∃ (ε : Bool) (m : ℕ), 2 * m = n ∧ IsStdSpace ε q m := by
  obtain ⟨ε, m, hstd, hm⟩ := exists_isStdSpace q (PolarNondeg.of_forall hq)
  refine ⟨ε, m, ?_, hstd⟩
  have h := finrank_of_isStdSpace_arf hstd hm
  rw [Module.finrank_fin_fun] at h
  omega

end TwoRankSmall

open TwoRankSmall CFSG.Open

theorem card_le_sixteen_of_le_isometries {q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2)}
    (hq : timmesfeldNondegenerate q)
    {E : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))}
    (hEq : E ≤ timmesfeldIsometries q) (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  obtain ⟨ε, m, hm, hstd⟩ := exists_std_of_nondegenerate hq
  obtain rfl : m = 3 := by omega
  cases ε
  · obtain ⟨φ, hφ⟩ := hstd
    exact card_le_of_isometry φ hφ (fun F hF h2 => core_minus3 hF h2) hEq hE2
  · obtain ⟨φ, hφ⟩ := hstd
    exact card_le_of_isometry φ hφ (fun F hF h2 => core_plus3 hF h2) hEq hE2

theorem card_le_four_of_le_isometries {q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hq : timmesfeldNondegenerate q)
    {E : Subgroup ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))}
    (hEq : E ≤ timmesfeldIsometries q) (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  obtain ⟨ε, m, hm, hstd⟩ := exists_std_of_nondegenerate hq
  obtain rfl : m = 2 := by omega
  cases ε
  · obtain ⟨φ, hφ⟩ := hstd
    exact card_le_of_isometry φ hφ (fun F hF h2 => core_minus2 hF h2) hEq hE2
  · obtain ⟨φ, hφ⟩ := hstd
    exact card_le_of_isometry φ hφ (fun F hF h2 => core_plus2 hF h2) hEq hE2

end CFSG.GF2Type.Smith1980Orth
