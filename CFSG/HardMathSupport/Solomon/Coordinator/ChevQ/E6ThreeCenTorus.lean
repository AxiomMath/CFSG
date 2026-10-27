module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoNormal
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenReps

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.StandardType.TableBExc.E6Three (gE6 cE6 wordE6G0 wordE6G1 wordE6G2 wordE6C gE6_comm
  gE6_pow_three)

set_option linter.unusedSectionVars false

local instance e6CenTorusNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def e6CenTz (a b c : ZMod 3) : Fin Tag.E6.rank → ZMod 3 :=
  ![a, b, a, c, -a - b, -a - b]

@[expose] def e6CenZWord : List (Fin Tag.E6.rank) := wordE6G0 ++ wordE6G1 ++ wordE6G2

theorem e6CenZ_eq_wordProd : e6CenZ = (coxeterSystem Tag.E6).wordProd e6CenZWord := by
  rw [e6CenZWord, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append]
  rfl

theorem e6CenZ_pow_three : e6CenZ ^ 3 = 1 := by
  have h2 : Commute (gE6 0 * gE6 1) (gE6 2) := Commute.mul_left (gE6_comm 0 2) (gE6_comm 1 2)
  have h01 : Commute (gE6 0) (gE6 1) := gE6_comm 0 1
  rw [e6CenZ, h2.mul_pow, h01.mul_pow, gE6_pow_three, gE6_pow_three, gE6_pow_three, one_mul,
    one_mul]

theorem e6Cen_g0g1sq_eq_wordProd :
    gE6 0 * gE6 1 ^ 2 = (coxeterSystem Tag.E6).wordProd (wordE6G0 ++ wordE6G1 ++ wordE6G1) := by
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, pow_two, ← mul_assoc]
  rfl

theorem e6Cen_fix_z : ∀ a b c d e f : ZMod 3,
    e6Wact e6CenZWord (e6ConjVec a b c d e f) = e6ConjVec a b c d e f →
      e6ConjVec a b c d e f = e6CenTz a b d := by
  decide +kernel

theorem e6Cen_fix_g0 : ∀ a b d : ZMod 3,
    e6Wact wordE6G0 (e6CenTz a b d) = e6CenTz a b d → a = 0 := by
  decide +kernel

theorem e6Cen_fix_g0g1sq : ∀ a b d : ZMod 3,
    e6Wact (wordE6G0 ++ wordE6G1 ++ wordE6G1) (e6CenTz a b d) = e6CenTz a b d → a = b := by
  decide +kernel

theorem e6Cen_fix_c : ∀ a b d : ZMod 3,
    e6Wact wordE6C (e6CenTz a b d) = e6CenTz a b d → a = b := by
  decide +kernel

@[expose] def e6CenTzKc (a b c : ZMod 3) : ℕ :=
  if a = b then if a = 0 ∧ c = 0 then 72 else 18 else 24

theorem e6Cen_kerCount_Tz : ∀ a b c : ZMod 3, e6KerCount (e6CenTz a b c) = e6CenTzKc a b c := by
  decide +kernel

theorem e6CenTz_add : ∀ a b c a' b' c' : ZMod 3,
    e6CenTz a b c + e6CenTz a' b' c' = e6CenTz (a + a') (b + b') (c + c') := by
  decide +kernel

theorem e6CenTz_smul : ∀ k a b c : ZMod 3, k • e6CenTz a b c = e6CenTz (k * a) (k * b) (k * c) := by
  decide +kernel

theorem e6CenTz_zero : e6CenTz 0 0 0 = 0 := by
  decide +kernel

@[expose] def e6CenLam (x : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  x 0 + 2 * x 2 + x 4 + 2 * x 5

theorem e6CenLam_Tz : ∀ a b c : ZMod 3, e6CenLam (e6CenTz a b c) = 0 := by
  decide +kernel

theorem e6CenLam_add (x y : Fin Tag.E6.rank → ZMod 3) :
    e6CenLam (x + y) = e6CenLam x + e6CenLam y := by
  simp only [e6CenLam, Pi.add_apply]
  ring

theorem e6Cen_kerCount_neg (x : Fin Tag.E6.rank → ZMod 3) : e6KerCount (-x) = e6KerCount x := by
  unfold e6KerCount
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_eq_zero]

theorem e6Cen_kerCount_zero : e6KerCount 0 = 72 := by
  decide +kernel

theorem e6Cen_add_self (x : Fin Tag.E6.rank → ZMod 3) : x + x = -x := by
  have h : ∀ a : ZMod 3, a + a = -a := by decide
  exact funext fun j => h (x j)

theorem e6Cen_vec_ids (x y : Fin Tag.E6.rank → ZMod 3) :
    x + x + y = -(x + y + y) ∧ y + y + x = x + y + y ∧ x + y + x = -(x + y + y) ∧
      x + y + (x + y) + x = -y ∧ x + y + y + x = -(x + y) ∧
      x + y + y + (x + y + y) + x = y := by
  have h : ∀ a b : ZMod 3, a + a + b = -(a + b + b) ∧ b + b + a = a + b + b ∧
      a + b + a = -(a + b + b) ∧ a + b + (a + b) + a = -b ∧ a + b + b + a = -(a + b) ∧
      a + b + b + (a + b + b) + a = b := by
    decide
  exact ⟨funext fun j => (h (x j) (y j)).1, funext fun j => (h (x j) (y j)).2.1,
    funext fun j => (h (x j) (y j)).2.2.1, funext fun j => (h (x j) (y j)).2.2.2.1,
    funext fun j => (h (x j) (y j)).2.2.2.2.1, funext fun j => (h (x j) (y j)).2.2.2.2.2⟩

@[expose] def E6CenCensusPat (x y : Fin Tag.E6.rank → ZMod 3) : Prop :=
  (e6KerCount x = 18 ∧ e6KerCount y = 24 ∧ e6KerCount (x + y) = 24 ∧
      e6KerCount (x + y + y) = 24) ∨
    (e6KerCount x = 24 ∧ e6KerCount y = 18 ∧ e6KerCount (x + y) = 24 ∧
      e6KerCount (x + y + y) = 24) ∨
    (e6KerCount x = 24 ∧ e6KerCount y = 24 ∧ e6KerCount (x + y) = 18 ∧
      e6KerCount (x + y + y) = 24) ∨
    (e6KerCount x = 24 ∧ e6KerCount y = 24 ∧ e6KerCount (x + y) = 24 ∧
      e6KerCount (x + y + y) = 18)

theorem e6Cen_O1_tab : ∀ a b c a' b' c' : ZMod 3, a ≠ b →
    (∀ k : ZMod 3, ¬ (a' = k * a ∧ b' = k * b ∧ c' = k * c)) →
    (e6CenTzKc a b c = 18 ∧ e6CenTzKc a' b' c' = 24 ∧
        e6CenTzKc (a + a') (b + b') (c + c') = 24 ∧
        e6CenTzKc (a + a' + a') (b + b' + b') (c + c' + c') = 24) ∨
      (e6CenTzKc a b c = 24 ∧ e6CenTzKc a' b' c' = 18 ∧
        e6CenTzKc (a + a') (b + b') (c + c') = 24 ∧
        e6CenTzKc (a + a' + a') (b + b' + b') (c + c' + c') = 24) ∨
      (e6CenTzKc a b c = 24 ∧ e6CenTzKc a' b' c' = 24 ∧
        e6CenTzKc (a + a') (b + b') (c + c') = 18 ∧
        e6CenTzKc (a + a' + a') (b + b' + b') (c + c' + c') = 24) ∨
      (e6CenTzKc a b c = 24 ∧ e6CenTzKc a' b' c' = 24 ∧
        e6CenTzKc (a + a') (b + b') (c + c') = 24 ∧
        e6CenTzKc (a + a' + a') (b + b' + b') (c + c' + c') = 18) := by
  decide +kernel

theorem e6Cen_O1_censusPat {a b c a' b' c' : ZMod 3} (hab : a ≠ b)
    (hspan : ∀ k : ZMod 3, ¬ (a' = k * a ∧ b' = k * b ∧ c' = k * c)) :
    E6CenCensusPat (e6CenTz a b c) (e6CenTz a' b' c') := by
  simp only [E6CenCensusPat, e6CenTz_add, e6Cen_kerCount_Tz]
  exact e6Cen_O1_tab a b c a' b' c' hab hspan

theorem e6Cen_mem_zpowers_three {G : Type*} [Group G] {g v : G} (hg : g ^ 3 = 1)
    (hv : v ∈ Subgroup.zpowers g) : v = 1 ∨ v = g ∨ v = g ^ 2 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  have hg' : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  rw [zpow_eq_zpow_emod m hg']
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> rw [hm]
  · exact Or.inl (zpow_zero g)
  · exact Or.inr (Or.inl (zpow_one g))
  · exact Or.inr (Or.inr (by norm_cast))

section Torus

variable {K : Type} [Field K]
  {ω : Kˣ}

theorem e6Cen_torV_injective (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {x y : Fin Tag.E6.rank → ZMod 3}
    (h : torV ω x = torV ω y) : x = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprim : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h3 h1)
  funext i
  exact ZMod.val_injective 3 (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (congrFun h i))

theorem e6Cen_torV_zero : torV ω (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
  funext i
  simp [torV]

theorem e6Cen_torV_pow_three (h3 : ω ^ 3 = 1) (x : Fin Tag.E6.rank → ZMod 3) :
    torV ω x ^ 3 = 1 := by
  funext i
  simp only [Pi.pow_apply, torV, Pi.one_apply]
  rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]

theorem e6Cen_torV_zpow (h3 : ω ^ 3 = 1) (x : Fin Tag.E6.rank → ZMod 3) (m : ℤ) :
    torV ω x ^ m = torV ω 0 ∨ torV ω x ^ m = torV ω x ∨ torV ω x ^ m = torV ω (x + x) := by
  rcases e6Cen_mem_zpowers_three (e6Cen_torV_pow_three h3 x)
    (Subgroup.zpow_mem_zpowers (torV ω x) m) with h | h | h
  · exact Or.inl (h.trans e6Cen_torV_zero.symm)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [h, e6PW_torV_add h3, pow_two]))

end Torus

section Census

variable
  {K : Type} [Field K] {ω : Kˣ}

theorem e6Cen_rootDiagUnit_torV_mem {x : Fin Tag.E6.rank → ZMod 3} (hx : e6CenLam x = 0) :
    rootDiagUnit Tag.E6 (torV ω x) ∈ adjointGroup Tag.E6 K := by
  have key : ∀ a b c d : ZMod 3, a + 2 * b + c + 2 * d = 0 →
      ((a.val : ℤ) + 2 * (b.val : ℤ) + (c.val : ℤ) + 2 * (d.val : ℤ)) % 3 = 0 := by
    decide +kernel
  obtain ⟨z, hz⟩ := bm_inner_exp (fun j => ((x j).val : ℤ)) (key (x 0) (x 2) (x 4) (x 5) hx)
  have e : torV ω x = fun j => ω ^ ∑ i, z i * Tag.E6.cartan i j := by
    funext j
    rw [hz j]
    simp only [torV, zpow_natCast]
  rw [e]
  exact bm_rootDiagUnit_cartan_mem ω z

theorem e6Cen_rootDiagAutHom_torV_mem {x : Fin Tag.E6.rank → ZMod 3} (hx : e6CenLam x = 0) :
    rootDiagAutHom Tag.E6 K (torV ω x) ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
  ⟨⟨_, e6Cen_rootDiagUnit_torV_mem hx⟩, bm_conj_eq_rootDiagAutHom rfl⟩

theorem e6Cen_fix_of_commute (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {l : List (Fin Tag.E6.rank)}
    {X : MulAut (adjointGroup Tag.E6 K)} (hX : BmMono X ((coxeterSystem Tag.E6).wordProd l))
    {x : Fin Tag.E6.rank → ZMod 3}
    (hc : X * rootDiagAutHom Tag.E6 K (torV ω x) = rootDiagAutHom Tag.E6 K (torV ω x) * X) :
    e6Wact l x = x := by
  obtain ⟨n, a, hn, hnv, rfl⟩ := hX
  refine e6Cen_torV_injective h3 h1 ?_
  rw [← weylTuple_prod_torV h3]
  exact bm_weylTuple_eq_of_commute hn hnv a _ hc

theorem e6Cen_torV_of_commute (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {l : List (Fin Tag.E6.rank)}
    {X : MulAut (adjointGroup Tag.E6 K)} (hX : BmMono X ((coxeterSystem Tag.E6).wordProd l))
    {b : Fin Tag.E6.rank → Kˣ} (hb3 : rootDiagAutHom Tag.E6 K b ^ 3 = 1)
    (hc : X * rootDiagAutHom Tag.E6 K b = rootDiagAutHom Tag.E6 K b * X) :
    ∃ x : Fin Tag.E6.rank → ZMod 3, b = torV ω x ∧ e6Wact l x = x := by
  have e : b ^ 3 = 1 := rootDiagAutHom_injective (τ := Tag.E6) (K := K)
    (show rootDiagAutHom Tag.E6 K (b ^ 3) = rootDiagAutHom Tag.E6 K 1 by
      rw [map_pow, hb3, map_one])
  obtain ⟨x, rfl⟩ := e6PW_exists_torV h3 h1 fun i => congrFun e i
  exact ⟨x, rfl, e6Cen_fix_of_commute h3 h1 hX hc⟩

theorem e6Cen_diag_mem_frame (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    {Z : MulAut (adjointGroup Tag.E6 K)} (hZE : Z ∈ E) (hZ : BmMono Z e6CenZ)
    {Y : MulAut (adjointGroup Tag.E6 K)} (hYE : Y ∈ E) (hY : BmMono Y 1) :
    ∃ a b c : ZMod 3, Y = rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b c)) := by
  obtain ⟨t, rfl⟩ := hY.exists_eq_rootDiag
  have hc : Z * rootDiagAutHom Tag.E6 K t = rootDiagAutHom Tag.E6 K t * Z :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨Z, hZE⟩ : E) ⟨_, hYE⟩)
  rw [e6CenZ_eq_wordProd] at hZ
  obtain ⟨x, rfl, hx⟩ := e6Cen_torV_of_commute h3 h1 hZ (hE.2 _ hYE) hc
  have e : x = e6ConjVec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext i
    fin_cases i <;> rfl
  refine ⟨x 0, x 1, x 3, ?_⟩
  rw [← e6Cen_fix_z (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (by rw [← e]; exact hx), ← e]

theorem e6Cen_inner_of_bmMono_one (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    {Z : MulAut (adjointGroup Tag.E6 K)} (hZE : Z ∈ E) (hZ : BmMono Z e6CenZ)
    {Y : MulAut (adjointGroup Tag.E6 K)} (hYE : Y ∈ E) (hY : BmMono Y 1) :
    Y ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  obtain ⟨a, b, c, rfl⟩ := e6Cen_diag_mem_frame h3 h1 hE hZE hZ hYE hY
  exact e6Cen_rootDiagAutHom_torV_mem (e6CenLam_Tz a b c)

theorem e6Cen_Tz_fix_g0 (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {X : MulAut (adjointGroup Tag.E6 K)}
    (hX : BmMono X (gE6 0)) {a b d : ZMod 3}
    (hc : X * rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b d)) =
      rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b d)) * X) : a = 0 :=
  e6Cen_fix_g0 a b d (e6Cen_fix_of_commute (l := wordE6G0) h3 h1 hX hc)

theorem e6Cen_Tz_fix_g0g1sq (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {X : MulAut (adjointGroup Tag.E6 K)}
    (hX : BmMono X (gE6 0 * gE6 1 ^ 2)) {a b d : ZMod 3}
    (hc : X * rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b d)) =
      rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b d)) * X) : a = b := by
  rw [e6Cen_g0g1sq_eq_wordProd] at hX
  exact e6Cen_fix_g0g1sq a b d (e6Cen_fix_of_commute h3 h1 hX hc)

theorem e6Cen_Tz_fix_c (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {X : MulAut (adjointGroup Tag.E6 K)}
    (hX : BmMono X cE6) {a b d : ZMod 3}
    (hc : X * rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b d)) =
      rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b d)) * X) : a = b :=
  e6Cen_fix_c a b d (e6Cen_fix_of_commute (l := wordE6C) h3 h1 hX hc)

theorem e6CenConcl_of_torV (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {x y : Fin Tag.E6.rank → ZMod 3}
    (hx : rootDiagAutHom Tag.E6 K (torV ω x) ∈ E) (hy : rootDiagAutHom Tag.E6 K (torV ω y) ∈ E)
    (hxl : e6CenLam x = 0) (hyl : e6CenLam y = 0) (h18 : e6KerCount x = 18)
    (h24 : e6KerCount y = 24) (h24' : e6KerCount (x + y) = 24)
    (h24'' : e6KerCount (x + x + y) = 24) : E6CenConcl K E := by
  obtain ⟨s, hs⟩ : ∃ s : adjointGroup Tag.E6 K,
      (s : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 (torV ω x) :=
    ⟨⟨_, e6Cen_rootDiagUnit_torV_mem hxl⟩, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : adjointGroup Tag.E6 K,
      (u : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 (torV ω y) :=
    ⟨⟨_, e6Cen_rootDiagUnit_torV_mem hyl⟩, rfl⟩
  have hsc := bm_conj_eq_rootDiagAutHom hs
  have huc := bm_conj_eq_rootDiagAutHom hu
  have hdim := e6PW_finrank_torV (K := K) h3 h1
  refine ⟨s, u, by rw [hsc]; exact hx, by rw [huc]; exact hy, ?_, by rw [hs, hdim, h18],
    fun k hk => ?_⟩
  · rw [hsc, huc]
    intro hm
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hm
    rw [← map_zpow] at hm
    have e := rootDiagAutHom_injective (τ := Tag.E6) (K := K) hm
    have hne : ∀ v : Fin Tag.E6.rank → ZMod 3, torV ω x ^ m = torV ω v →
        e6KerCount v ≠ 24 → False := fun v hv hv24 =>
      hv24 (by rw [e6Cen_torV_injective h3 h1 (hv.symm.trans e)]; exact h24)
    rcases e6Cen_torV_zpow h3 x m with h | h | h
    · exact hne 0 h (by rw [e6Cen_kerCount_zero]; decide)
    · exact hne x h (by rw [h18]; decide)
    · exact hne (x + x) h (by rw [e6Cen_add_self, e6Cen_kerCount_neg, h18]; decide)
  · interval_cases k
    · rw [pow_zero, one_mul, hu, hdim, h24]
    · have e : ((s ^ 1 * u : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          rootDiagUnit Tag.E6 (torV ω (x + y)) := by
        rw [pow_one, Subgroup.coe_mul, hs, hu, e6PW_torV_add h3, e6PW_rootDiagUnit_mul]
      rw [e, hdim, h24']
    · have e : ((s ^ 2 * u : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          rootDiagUnit Tag.E6 (torV ω (x + x + y)) := by
        rw [pow_two, Subgroup.coe_mul, Subgroup.coe_mul, hs, hu, e6PW_torV_add h3,
          e6PW_torV_add h3, e6PW_rootDiagUnit_mul, e6PW_rootDiagUnit_mul]
      rw [e, hdim, h24'']

theorem e6CenConcl_of_censusPat (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} {x y : Fin Tag.E6.rank → ZMod 3}
    (hx : rootDiagAutHom Tag.E6 K (torV ω x) ∈ E) (hy : rootDiagAutHom Tag.E6 K (torV ω y) ∈ E)
    (hxl : e6CenLam x = 0) (hyl : e6CenLam y = 0) (hpat : E6CenCensusPat x y) :
    E6CenConcl K E := by
  have hxy : rootDiagAutHom Tag.E6 K (torV ω (x + y)) ∈ E := by
    rw [e6PW_torV_add h3, map_mul]
    exact mul_mem hx hy
  have hxyy : rootDiagAutHom Tag.E6 K (torV ω (x + y + y)) ∈ E := by
    rw [e6PW_torV_add h3, map_mul]
    exact mul_mem hxy hy
  have hxyl : e6CenLam (x + y) = 0 := by rw [e6CenLam_add, hxl, hyl, add_zero]
  have hxyyl : e6CenLam (x + y + y) = 0 := by rw [e6CenLam_add, hxyl, hyl, add_zero]
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := e6Cen_vec_ids x y
  rcases hpat with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · exact e6CenConcl_of_torV h3 h1 hx hy hxl hyl ha hb hc
      (by rw [i1, e6Cen_kerCount_neg, hd])
  · exact e6CenConcl_of_torV h3 h1 hy hx hyl hxl hb ha (by rw [add_comm, hc])
      (by rw [i2, hd])
  · exact e6CenConcl_of_torV h3 h1 hxy hx hxyl hxl hc ha (by rw [i3, e6Cen_kerCount_neg, hd])
      (by rw [i4, e6Cen_kerCount_neg, hb])
  · exact e6CenConcl_of_torV h3 h1 hxyy hx hxyyl hxl hd ha
      (by rw [i5, e6Cen_kerCount_neg, hc]) (by rw [i6, hb])

theorem e6Cen_exists_inner_notMem [Finite K] {E : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) (hED : E ≤ e6Inndiag K)
    (hEi : ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K))
    {σ : MulAut (adjointGroup Tag.E6 K)} (hσ : σ ∈ E) :
    ∃ u ∈ E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K), u ∉ Subgroup.zpowers σ := by
  by_contra hno
  push Not at hno
  have h9 : Nat.card ↥(E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) = 3 ^ 2 :=
    card_inf_innerAut_of_le_e6Inndiag K hEc hED hEi
  have hdvd := Subgroup.card_dvd_of_le
    (show E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) ≤ Subgroup.zpowers σ from hno)
  rw [h9, Nat.card_zpowers] at hdvd
  have h33 := Nat.dvd_trans hdvd (orderOf_dvd_of_pow_eq_one (hE.2 σ hσ))
  norm_num at h33

theorem e6Cen_O1_bmMono_one (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hEi : ¬ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) (hF : E6CenFrame e6CenO1 E)
    {Y : MulAut (adjointGroup Tag.E6 K)} (hYE : Y ∈ E)
    (hYi : Y ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) : BmMono Y 1 := by
  obtain ⟨Z, hZE, hZ⟩ := hF.2 e6CenZ (Subgroup.mem_zpowers _)
  have hd : ∀ Y' ∈ E, BmMono Y' 1 → Y' ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
    fun Y' hY'E hY' => e6Cen_inner_of_bmMono_one h3 h1 hE hZE hZ hY'E hY'
  have hz : ∀ W ∈ E, W ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) → BmMono W e6CenZ →
      False := by
    intro W hWE hWi hW
    refine hEi fun Y' hY'E => ?_
    obtain ⟨v, hv, hY'v⟩ := hF.1 Y' hY'E
    rcases e6Cen_mem_zpowers_three e6CenZ_pow_three hv with rfl | rfl | rfl
    · exact hd Y' hY'E hY'v
    · have h' := hY'v.mul hW.inv
      rw [mul_inv_cancel] at h'
      have := mul_mem (hd _ (mul_mem hY'E (inv_mem hWE)) h') hWi
      rwa [inv_mul_cancel_right] at this
    · have h' := (hY'v.mul hW.inv).mul hW.inv
      rw [show e6CenZ ^ 2 * e6CenZ⁻¹ * e6CenZ⁻¹ = 1 by group] at h'
      have := mul_mem (mul_mem (hd _ (mul_mem (mul_mem hY'E (inv_mem hWE)) (inv_mem hWE)) h')
        hWi) hWi
      rwa [show Y' * W⁻¹ * W⁻¹ * W * W = Y' by group] at this
  obtain ⟨v, hv, hYv⟩ := hF.1 Y hYE
  rcases e6Cen_mem_zpowers_three e6CenZ_pow_three hv with rfl | rfl | rfl
  · exact hYv
  · exact (hz Y hYE hYi hYv).elim
  · have h2 := hYv.pow 2
    rw [← pow_mul, show e6CenZ ^ (2 * 2) = e6CenZ by
      rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, e6CenZ_pow_three, one_mul]] at h2
    exact (hz _ (pow_mem hYE 2) (pow_mem hYi 2) h2).elim

theorem e6Cen_O1 [Finite K] (hK4 : 4 ≤ Nat.card K) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcube : E6CenCube K E)
    (hF : E6CenFrame e6CenO1 E) : E6CenConcl K E := by
  obtain ⟨hE, hEc, hED, hEi, -, hA⟩ := hcube
  obtain ⟨Z, hZE, hZ⟩ := hF.2 e6CenZ (Subgroup.mem_zpowers _)
  have hdiag : ∀ Y ∈ E, Y ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) →
      ∃ a b c : ZMod 3, Y = rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b c)) :=
    fun Y hYE hYi => e6Cen_diag_mem_frame h3 h1 hE hZE hZ hYE
      (e6Cen_O1_bmMono_one h3 h1 hE hEi hF hYE hYi)
  simp only [E6InnerAll24, not_forall] at hA
  obtain ⟨s, hs, hs1, hs24⟩ := hA
  obtain ⟨a, b, c, hsx⟩ := hdiag _ hs ⟨s, rfl⟩
  have hsx' := e6Cen_coe_eq_of_conj_eq_rootDiag hK4 hsx
  have hab : a ≠ b := by
    intro hab
    subst hab
    by_cases hac : a = 0 ∧ c = 0
    · obtain ⟨rfl, rfl⟩ := hac
      refine hs1 (Subtype.ext ?_)
      rw [hsx', e6CenTz_zero, e6Cen_torV_zero, OneMemClass.coe_one]
      exact Units.ext rootDiag_one
    · refine hs24 ?_
      rw [hsx', e6PW_finrank_torV h3 h1, e6Cen_kerCount_Tz, e6CenTzKc, if_pos rfl, if_neg hac]
  obtain ⟨u', ⟨huE, hui⟩, hu'⟩ := e6Cen_exists_inner_notMem hE hEc hED hEi hs
  obtain ⟨a', b', c', rfl⟩ := hdiag _ huE hui
  have hspan : ∀ k : ZMod 3, ¬ (a' = k * a ∧ b' = k * b ∧ c' = k * c) := by
    rintro k ⟨rfl, rfl, rfl⟩
    refine hu' (Subgroup.mem_zpowers_iff.2 ⟨(k.val : ℤ), ?_⟩)
    rw [zpow_natCast, hsx, ← map_pow, ← e6PW_torV_smul h3, e6CenTz_smul]
  exact e6CenConcl_of_censusPat h3 h1 (by rw [← hsx]; exact hs) huE (e6CenLam_Tz a b c)
    (e6CenLam_Tz a' b' c') (e6Cen_O1_censusPat hab hspan)

end Census

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
