module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Code
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerCode

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup GL62.Code

theorem mAct_eq (m v : ℕ) : SCATWreath.mAct m v = act m v := rfl

theorem mMul_eq (a b : ℕ) : SCATWreath.mMul a b = mul a b := rfl

theorem vec_xor (a b : ℕ) : vec (a ^^^ b) = vec a + vec b := by
  funext i
  exact bitZ_xor a b i

theorem vec_zero : vec 0 = 0 := by
  funext i
  simp [vec, bitZ]

theorem vec_inj {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : vec a = vec b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 6
  · exact testBit_eq_of_bitZ_eq (congrFun h ⟨k, hk⟩)
  · have h6 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem vec_surj (v : Fin 6 → ZMod 2) : ∃ m < 64, vec m = v := by
  have hinj : Function.Injective fun m : Fin 64 => vec m.1 :=
    fun a b h => Fin.ext (vec_inj a.2 b.2 h)
  have hcard : Fintype.card (Fin 64) = Fintype.card (Fin 6 → ZMod 2) := by simp
  obtain ⟨m, hm⟩ := ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2 v
  exact ⟨m.1, m.2, hm⟩

@[expose] def subCheck (gc L : List ℕ) (par : List (ℕ × ℕ)) : Bool :=
  L.length == 128 && L.all (· < 2 ^ 36) && L[0]? == some GL62.Code.one &&
    L.all (fun c => gc.all fun g => L.contains (mul g c)) && par.length == 127 &&
    (List.range 127).all fun i =>
      par[i]!.1 < i + 1 && par[i]!.2 < gc.length && L[i + 1]! == mul gc[par[i]!.2]! L[par[i]!.1]!

structure SubModel (S : Subgroup (GL (Fin 6) (ZMod 2))) (L : List ℕ) : Prop where
  len : L.length = 128
  nodup : L.Nodup
  lt : ∀ c ∈ L, c < 2 ^ 36
  zero : L[0]! = GL62.Code.one
  mem_iff : ∀ g : GL (Fin 6) (ZMod 2),
    g ∈ S ↔ ∃ c ∈ L, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = mat c
  exists_mem : ∀ c ∈ L, ∃ g ∈ S, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = mat c

theorem subModel_of_check {gens : List (GL (Fin 6) (ZMod 2))} {gc L : List ℕ}
    {par : List (ℕ × ℕ)} (hgc : gc.map mat = gens.map Units.val)
    (hchk : subCheck gc L par = true) (hnd : L.Nodup) :
    SubModel (closure {x | x ∈ gens}) L := by
  classical
  simp only [subCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.contains_eq_mem, List.mem_range] at hchk
  obtain ⟨⟨⟨⟨⟨hlen, hlt⟩, h0⟩, hcl⟩, hpl⟩, hpar⟩ := hchk
  have hlen' : gc.length = gens.length := by
    have := congrArg List.length hgc
    simpa using this
  have hgen : ∀ k < gc.length, mat gc[k]! = (gens[k]! : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    intro k hk
    have hk' : k < gens.length := hlen' ▸ hk
    have h1 := congrArg (fun l => l[k]?) hgc
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk',
      Option.map_some, Option.some.injEq] at h1
    rw [getElem!_pos gc k hk, getElem!_pos gens k hk']
    exact h1
  have hL0 : L[0]! = GL62.Code.one := by
    rw [List.getElem!_eq_getElem?_getD, h0]
    rfl
  have key : ∀ i < 128, ∃ g ∈ closure {x | x ∈ gens},
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = mat L[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases i with _ | i
      · exact ⟨1, one_mem _, by rw [hL0, mat_one]; rfl⟩
      · obtain ⟨⟨hj, hk⟩, he⟩ := hpar i (by omega)
        obtain ⟨g', hg', hg'm⟩ := ih _ (by omega) (by omega)
        refine ⟨gens[par[i]!.2]! * g', mul_mem (subset_closure ?_) hg', ?_⟩
        · show gens[par[i]!.2]! ∈ gens
          rw [getElem!_pos gens _ (hlen' ▸ hk)]
          exact List.getElem_mem _
        · rw [he, mat_mul, Units.val_mul, hg'm, hgen _ hk]
  have hex : ∀ c ∈ L, ∃ g ∈ closure {x | x ∈ gens},
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = mat c := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨g', hg', hg'm⟩ := key i (by omega)
    exact ⟨g', hg', by rw [hg'm, getElem!_pos L i hi]⟩
  refine ⟨hlen, hnd, hlt, hL0, fun g => ⟨fun hg => ?_, fun ⟨c, hc, hgc'⟩ => ?_⟩, hex⟩
  ·
    have hfin : (closure {x | x ∈ gens}).toSubmonoid = Submonoid.closure {x | x ∈ gens} :=
      Subgroup.closure_toSubmonoid_of_finite
    have hg' : g ∈ Submonoid.closure {x | x ∈ gens} := by
      rw [← hfin]
      exact hg
    clear hg
    induction hg' using Submonoid.closure_induction_left with
    | one => exact ⟨GL62.Code.one, List.mem_of_getElem? h0, by rw [mat_one]; rfl⟩
    | mul_left x hx y _ ih =>
      obtain ⟨c, hc, hyc⟩ := ih
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show x ∈ gens from hx)
      have hk' : k < gc.length := hlen' ▸ hk
      have hgk : gc[k]! ∈ gc := by
        rw [getElem!_pos gc k hk']
        exact List.getElem_mem _
      refine ⟨mul gc[k]! c, hcl c hc _ hgk, ?_⟩
      rw [Units.val_mul, mat_mul, hyc, hgen k hk', getElem!_pos gens k hk]
  ·
    obtain ⟨g', hg', hg'm⟩ := hex c hc
    have hgg : g = g' := Units.ext (by rw [hgc', hg'm])
    rw [hgg]
    exact hg'

theorem wrS_eq_closure :
    wrS = closure {x | x ∈ [GL62.z₀, GL62.dg e12, GL62.dg e23, wrH₁, wrH₂]} := by
  rw [wrS]
  congr 1
  ext x
  simp

theorem slS_eq_closure :
    slS = closure {x | x ∈ [GL62.z₀, GL62.dg e12, GL62.dg e23, slH₁, slH₂]} := by
  rw [slS]
  congr 1
  ext x
  simp

theorem wrGens_mat : SCATWreath.wrGens.map mat =
    [GL62.z₀, GL62.dg e12, GL62.dg e23, wrH₁, wrH₂].map Units.val := by
  decide

theorem slGens_mat : SCATWreath.slGens.map mat =
    [GL62.z₀, GL62.dg e12, GL62.dg e23, slH₁, slH₂].map Units.val := by
  decide

theorem subModel_wr : SubModel wrS SCATWreath.wrList := by
  rw [wrS_eq_closure]
  exact subModel_of_check (par := SCATWreath.wrPar) wrGens_mat (by decide +kernel)
    (by decide +kernel)

theorem subModel_sl : SubModel slS SCATWreath.slList := by
  rw [slS_eq_closure]
  exact subModel_of_check (par := SCATWreath.slPar) slGens_mat (by decide +kernel)
    (by decide +kernel)

variable {S : Subgroup (GL (Fin 6) (ZMod 2))} {L : List ℕ}

namespace SubModel

variable (hS : SubModel S L)
include hS

theorem getElem_mem' {i : ℕ} (hi : i < 128) : L[i]! ∈ L := by
  rw [getElem!_pos L i (hS.len ▸ hi)]
  exact List.getElem_mem _

theorem lt' {i : ℕ} (hi : i < 128) : L[i]! < 2 ^ 36 := hS.lt _ (hS.getElem_mem' hi)

noncomputable def sElt (i : ℕ) : S :=
  open Classical in
  if h : i < 128 then ⟨(hS.exists_mem _ (hS.getElem_mem' h)).choose,
    (hS.exists_mem _ (hS.getElem_mem' h)).choose_spec.1⟩ else 1

theorem sElt_mat {i : ℕ} (hi : i < 128) :
    (((hS.sElt i : S) : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = mat L[i]! := by
  rw [sElt, dif_pos hi]
  exact (hS.exists_mem _ (hS.getElem_mem' hi)).choose_spec.2

theorem sElt_eq_iff {i j : ℕ} (hi : i < 128) (hj : j < 128) : hS.sElt i = hS.sElt j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h1 : mat L[i]! = mat L[j]! := by
    rw [← hS.sElt_mat hi, ← hS.sElt_mat hj, h]
  have h2 := eq_of_mat_eq (hS.lt' hi) (hS.lt' hj) h1
  rw [getElem!_pos L i (hS.len ▸ hi), getElem!_pos L j (hS.len ▸ hj)] at h2
  exact (hS.nodup.getElem_inj_iff).1 h2

theorem exists_sElt (s : S) : ∃ i < 128, hS.sElt i = s := by
  obtain ⟨c, hc, hsc⟩ := (hS.mem_iff s).1 s.2
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < 128 := hS.len ▸ hi
  refine ⟨i, hi', Subtype.ext (Units.ext ?_)⟩
  rw [hS.sElt_mat hi', hsc, getElem!_pos L i hi]

theorem sElt_zero : hS.sElt 0 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [hS.sElt_mat (by norm_num), hS.zero, mat_one]
  rfl

theorem mul_mem' {i j : ℕ} (hi : i < 128) (hj : j < 128) : mul L[i]! L[j]! ∈ L := by
  obtain ⟨c, hc, hgc⟩ := (hS.mem_iff _).1 (hS.sElt i * hS.sElt j).2
  have h1 : mat c = mat (mul L[i]! L[j]!) := by
    rw [← hgc, mat_mul, ← hS.sElt_mat hi, ← hS.sElt_mat hj]
    rfl
  rwa [← eq_of_mat_eq (hS.lt c hc) (mul_lt _ _) h1]

theorem sElt_mul {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    hS.sElt (L.idxOf (mul L[i]! L[j]!)) = hS.sElt i * hS.sElt j := by
  have hm := hS.mul_mem' hi hj
  have hk := List.idxOf_lt_length_of_mem hm
  have hk' : L.idxOf (mul L[i]! L[j]!) < 128 := hS.len ▸ hk
  refine Subtype.ext (Units.ext ?_)
  rw [hS.sElt_mat hk', getElem!_pos L _ hk, List.getElem_idxOf hk]
  show mat (mul L[i]! L[j]!) = _
  rw [mat_mul, ← hS.sElt_mat hi, ← hS.sElt_mat hj]
  rfl

theorem idxOf_lt {i j : ℕ} (hi : i < 128) (hj : j < 128) : L.idxOf (mul L[i]! L[j]!) < 128 :=
  hS.len ▸ List.idxOf_lt_length_of_mem (hS.mul_mem' hi hj)

theorem smulTab_get {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    (SCATWreath.smulTab L)[i * 128 + j]! = L.idxOf (mul L[i]! L[j]!) := by
  have hk : i * 128 + j < 128 * 128 := by omega
  rw [SCATWreath.smulTab, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]
  simp only [List.getElem!_toArray]
  rw [show (i * 128 + j) / 128 = i by omega, show (i * 128 + j) % 128 = j by omega]
  rfl

theorem actTab_get {i v : ℕ} (hi : i < 128) (hv : v < 64) :
    (SCATWreath.actTab L)[i * 64 + v]! = act L[i]! v := by
  have hk : i * 64 + v < 128 * 64 := by omega
  rw [SCATWreath.actTab, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]
  simp only [List.getElem!_toArray]
  rw [show (i * 64 + v) / 64 = i by omega, show (i * 64 + v) % 64 = v by omega]
  rfl

@[expose] noncomputable def decW (c : ℕ) : Grp S :=
  ⟨Multiplicative.ofAdd (vec (c % 64)), hS.sElt (c / 64)⟩

theorem decW_left (c : ℕ) : (hS.decW c).left = Multiplicative.ofAdd (vec (c % 64)) := rfl

theorem decW_right (c : ℕ) : (hS.decW c).right = hS.sElt (c / 64) := rfl

theorem isModel_decW :
    IsModel (⊤ : Subgroup (Grp S)) 8192 (SCATWreath.wMul (SCATWreath.smulTab L)
      (SCATWreath.actTab L)) hS.decW := by
  have hdiv : ∀ c < 8192, c / 64 < 128 := fun c hc => by omega
  have hmod : ∀ c, c % 64 < 64 := fun c => Nat.mod_lt _ (by norm_num)
  have hwm : ∀ a < 8192, ∀ b < 8192, SCATWreath.wMul (SCATWreath.smulTab L)
      (SCATWreath.actTab L) a b = 64 * L.idxOf (mul L[a / 64]! L[b / 64]!) +
        (a % 64 ^^^ act L[a / 64]! (b % 64)) := by
    intro a ha b hb
    rw [SCATWreath.wMul, hS.smulTab_get (hdiv a ha) (hdiv b hb),
      hS.actTab_get (hdiv a ha) (hmod b)]
  have hxor : ∀ a b, a % 64 ^^^ act (L[a / 64]!) (b % 64) < 64 := fun a b =>
    Nat.xor_lt_two_pow (n := 6) (by simpa using hmod a) (by simpa using act_lt _ _)
  refine ⟨fun c _ => mem_top _, fun a ha b hb h => ?_, fun x _ => ?_, fun a ha b hb => ?_,
    fun a ha b hb => ?_, by norm_num, ?_⟩
  ·
    have h1 := congrArg SemidirectProduct.left h
    have h2 := congrArg SemidirectProduct.right h
    rw [decW_left, decW_left] at h1
    rw [decW_right, decW_right] at h2
    have e1 := vec_inj (hmod a) (hmod b) (Multiplicative.ofAdd.injective h1)
    have e2 := (hS.sElt_eq_iff (hdiv a ha) (hdiv b hb)).1 h2
    omega
  ·
    obtain ⟨i, hi, hix⟩ := hS.exists_sElt x.right
    obtain ⟨m, hm, hmx⟩ := vec_surj (Multiplicative.toAdd x.left)
    refine ⟨64 * i + m, by omega, SemidirectProduct.ext ?_ ?_⟩
    · rw [decW_left, show (64 * i + m) % 64 = m by omega, hmx]
      rfl
    · rw [decW_right, show (64 * i + m) / 64 = i by omega, hix]
  ·
    rw [hwm a ha b hb]
    have := hS.idxOf_lt (hdiv a ha) (hdiv b hb)
    have := hxor a b
    omega
  ·
    rw [hwm a ha b hb]
    have hk := hS.idxOf_lt (hdiv a ha) (hdiv b hb)
    have hx := hxor a b
    refine SemidirectProduct.ext ?_ ?_
    · rw [decW_left, show (64 * L.idxOf (mul L[a / 64]! L[b / 64]!) +
        (a % 64 ^^^ act L[a / 64]! (b % 64))) % 64 = a % 64 ^^^ act L[a / 64]! (b % 64) by omega,
        SemidirectProduct.mul_left, decW_left, decW_left, decW_right, affAct_apply, vec_xor,
        vec_act, hS.sElt_mat (hdiv a ha)]
      rfl
    · rw [decW_right, show (64 * L.idxOf (mul L[a / 64]! L[b / 64]!) +
        (a % 64 ^^^ act L[a / 64]! (b % 64))) / 64 = L.idxOf (mul L[a / 64]! L[b / 64]!) by omega,
        SemidirectProduct.mul_right, decW_right, decW_right, hS.sElt_mul (hdiv a ha) (hdiv b hb)]
  ·
    refine SemidirectProduct.ext ?_ ?_
    · rw [decW_left, Nat.zero_mod, vec_zero]
      rfl
    · rw [decW_right, Nat.zero_div, hS.sElt_zero]
      rfl

theorem decW_64 (hz : mat L[1]! = (GL62.z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (h0 : GL62.z₀ ∈ S) : hS.decW 64 = t₀ S h0 := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [decW_left, show 64 % 64 = 0 by norm_num, vec_zero]
    rfl
  · rw [decW_right, show 64 / 64 = 1 by norm_num, t₀_right]
    exact Subtype.ext (Units.ext (by rw [hS.sElt_mat (by norm_num), hz]))

end SubModel

theorem IsModel.map_range {G H : Type*} [Group G] [Group H] {n : ℕ} {mul : ℕ → ℕ → ℕ}
    {dec : ℕ → H} (M : IsModel (⊤ : Subgroup H) n mul dec) (ι : H →* G)
    (hι : Function.Injective ι) : IsModel ι.range n mul (ι ∘ dec) where
  mem c _ := ⟨dec c, rfl⟩
  inj a ha b hb h := M.inj a ha b hb (hι h)
  surj x hx := by
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := M.surj y (mem_top y)
    exact ⟨c, hc, rfl⟩
  mul_lt := M.mul_lt
  dec_mul a ha b hb := by
    simp only [Function.comp_apply]
    rw [M.dec_mul a ha b hb, map_mul]
  zero_lt := M.zero_lt
  dec_zero := by simp [M.dec_zero]

theorem mat_wr1 : mat SCATWreath.wrList[1]! = (GL62.z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  decide

theorem mat_sl1 : mat SCATWreath.slList[1]! = (GL62.z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  decide

end CFSG.OddStandard.AltStdSmall4.Tower
