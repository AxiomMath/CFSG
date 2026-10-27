module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XFamily
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω} {G₀ : Type} [Group G₀]

private theorem type126_of_model_aux1 (M : S172X.S172Model S B G₀) : piImg M S = ⊤ := by
  rw [piImg, Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective M.π M.surj

private theorem type126_of_model_aux2 {G G' : Type} [Group G] [Group G'] {p : ℕ}
    {L K J : Subgroup G} {L' K' J' : Subgroup G'}
    (eL : PSimple p L ≃* PSimple p L') (eK : PSimple p K ≃* PSimple p K')
    (eJ : PSimple p J ≃* PSimple p J') : Type126 p L K J → Type126 p L' K' J' := by
  rintro (⟨hp, n, hn, hL, hK, hJ⟩ | ⟨hp, n, hn, hL, hK, hJ⟩ | ⟨n, k, hn, hk, hdiv, hL, hK, hJ⟩)
  · subst p
    exact Or.inl ⟨rfl, n, hn, (catalogIs_congr eL).1 hL, (catalogIs_congr eK).1 hK, (catalogIs_congr eJ).1 hJ⟩
  · subst p
    exact Or.inr (Or.inl ⟨rfl, n, hn, (catalogIs_congr eL).1 hL, (catalogIs_congr eK).1 hK, (catalogIs_congr eJ).1 hJ⟩)
  · exact Or.inr (Or.inr ⟨n, k, hn, hk, hdiv, (catalogIs_congr eL).1 hL, (catalogIs_congr eK).1 hK,
      (catalogIs_congr eJ).1 hJ⟩)

theorem type126_of_model [Finite G₀] (hp : p.Prime) (M : S172X.S172Model S B G₀) (hSp : Group.IsPerfect ↥S)
    {K I : Subgroup Ω} (hKS : K ≤ S) (hIS : I ≤ S) (hK : Group.IsPerfect ↥K) (hI : Group.IsPerfect ↥I)
    {K₀ I₀ : Subgroup G₀} (hK₀ : piImg M K = K₀) (hI₀ : piImg M I = I₀)
    (h : Type126 p (⊤ : Subgroup G₀) K₀ I₀) : Type126 p S K I := by
  obtain ⟨eS⟩ := nonempty_pSimple_equiv_piImg M hp le_rfl hSp
  rw [type126_of_model_aux1 M] at eS
  obtain ⟨eK⟩ := nonempty_pSimple_equiv_piImg M hp hKS hK
  rw [hK₀] at eK
  obtain ⟨eI⟩ := nonempty_pSimple_equiv_piImg M hp hIS hI
  rw [hI₀] at eI
  exact type126_of_model_aux2 eS.symm eK.symm eI.symm h

theorem exists_two_subgroup_le_K (hcfg : Cfg173 p S B N D K x) :
    ∃ U : Subgroup Ω, U ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U := by
  have hqs : CFSG.Open.IsQuasisimple ↥K := hcfg.std.2.2.2.2.2.1.2.2
  haveI : Nontrivial ↥K := isQuasisimple_nontrivial hqs
  haveI : Group.IsPerfect ↥K := isPerfect_K hcfg
  have hnotsolv : ¬ Group.IsSolvable ↥K := Group.IsPerfect.not_isSolvable ↥K
  have hEven : Even (Nat.card ↥K) := by
    by_contra h
    exact hnotsolv (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp h))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (even_iff_two_dvd.mp hEven)
  have ho : orderOf (t : Ω) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hne : (t : Ω) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ho
    omega
  refine ⟨Subgroup.zpowers (t : Ω), Subgroup.zpowers_le.2 t.2, ?_, ?_⟩
  · exact Subgroup.zpowers_eq_bot.not.mpr hne
  · exact IsPGroup.of_card (p := 2) (n := 1) (by simp [Nat.card_zpowers, ho])

private lemma exists_alt_iv_of_model_aux0 {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, y, hy, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  · rintro a b _ _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    refine ⟨a₁ * b₁, H.mul_mem ha₁ hb₁, a₂ * b₂, K.mul_mem ha₂ hb₂, ?_⟩
    calc (a₁ * b₁) * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [hc b₁ hb₁ a₂ ha₂]
      _ = (a₁ * a₂) * (b₁ * b₂) := by group
  · rintro a _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    refine ⟨a₁⁻¹, H.inv_mem ha₁, a₂⁻¹, K.inv_mem ha₂, ?_⟩
    rw [mul_inv_rev]
    exact hc a₁⁻¹ (H.inv_mem ha₁) a₂⁻¹ (K.inv_mem ha₂)

theorem piImg_inf_ker_eq_bot (M : S172X.S172Model S B G₀) {P : Subgroup Ω} (hPS : P ≤ S)
    {E : Subgroup G₀} (hPE : piImg M P = E) (hPcard : Nat.card P = Nat.card E) :
    P.subgroupOf S ⊓ M.π.ker = ⊥ := by
  let φ : ↥(P.subgroupOf S) →* G₀ := M.π.comp (P.subgroupOf S).subtype
  have hrange : φ.range = E := by
    rw [← hPE]
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact Subgroup.mem_map_of_mem M.π u.2
    · intro hg
      obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.1 hg
      exact ⟨⟨s, hs⟩, hsg⟩
  have hker : φ.ker.map (P.subgroupOf S).subtype = P.subgroupOf S ⊓ M.π.ker := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨hxP, hxker⟩
      exact ⟨⟨x, hxP⟩, hxker, rfl⟩
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hrange, ← hPcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv] at hcard
  have h1 : Nat.card φ.ker = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hcard, one_mul])
  have h2 : φ.ker = ⊥ := (Subgroup.eq_bot_iff_card φ.ker).2 h1
  rw [← hker, h2, Subgroup.map_bot]

theorem mem_of_piImg_of_pow_eq_one (M : S172X.S172Model S B G₀) {K' : Subgroup Ω} (hK'S : K' ≤ S)
    {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    {u : ↥S} (hu : M.π u ∈ piImg M K') (hup : u ^ p = 1) :
    (u : Ω) ∈ K' := by
  obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.1 hu
  have hk' : (k : Ω) ∈ K' := hk
  have hzmem : k⁻¹ * u ∈ Subgroup.center ↥S := by
    rw [← M.ker_π, MonoidHom.mem_ker, map_mul, map_inv, hkπ, inv_mul_cancel]
  set z : ↥S := k⁻¹ * u with hzdef
  have hu_eq : u = k * z := by rw [hzdef]; group
  have hcomm : Commute k z := Subgroup.mem_center_iff.1 hzmem k
  have hzp : z ^ p = (k ^ p)⁻¹ := by
    have h1 : (k * z) ^ p = k ^ p * z ^ p := hcomm.mul_pow p
    have h1' : k ^ p * z ^ p = 1 := by rw [← h1, ← hu_eq]; exact hup
    exact eq_inv_of_mul_eq_one_right h1'
  have hzpK : (z : Ω) ^ p ∈ K' := by
    have h2 : ((z : Ω) ^ p) = ((k : Ω) ^ p)⁻¹ := by
      simpa using congrArg (Subtype.val) hzp
    rw [h2]
    exact K'.inv_mem (K'.pow_mem hk' p)
  have hzK : (z : Ω) ∈ K' := by
    have hz2 : (z : Ω) ∈ Subgroup.zpowers ((z : Ω) ^ p) := by
      rw [mem_zpowers_pow_iff]
      refine hp.coprime_iff_not_dvd.mpr fun hd => hZ (hd.trans ?_)
      rw [Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard _ hzmem
    exact Subgroup.zpowers_le.2 hzpK hz2
  have hcoe : (u : Ω) = (k : Ω) * (z : Ω) := by rw [hu_eq, Subgroup.coe_mul]
  rw [hcoe]
  exact K'.mul_mem hk' hzK

private lemma exists_alt_iv_of_model_aux3 (M : S172X.S172Model S B G₀) {K' : Subgroup Ω} (hK'S : K' ≤ S)
    (hK' : Group.IsPerfect ↥K') {u : ↥S}
    (hu : M.π u ∈ Subgroup.centralizer (piImg M K' : Set G₀)) :
    (u : Ω) ∈ Subgroup.centralizer (K' : Set Ω) := by
  haveI : Group.IsPerfect ↥(K'.subgroupOf S) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK'S).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK'S).symm.surjective
  have hcomm : ∀ d ∈ K'.subgroupOf S, ⁅u, d⁆ ∈ Subgroup.center ↥S := by
    intro d hd
    rw [commutatorElement_def, ← M.ker_π, MonoidHom.mem_ker,
      map_mul, map_mul, map_mul, map_inv, map_inv]
    have hdmem : M.π d ∈ piImg M K' := Subgroup.mem_map_of_mem M.π hd
    have hc := Subgroup.mem_centralizer_iff.1 hu (M.π d) hdmem
    rw [← hc]
    group
  have h := CFSG.SectionRank.commute_of_perfect_of_central_commutator (K'.subgroupOf S) u hcomm
  refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
  have hk' : (⟨k, hK'S hk⟩ : ↥S) ∈ K'.subgroupOf S := hk
  have hc := h ⟨k, hK'S hk⟩ hk'
  exact (Subtype.ext_iff.mp hc.eq).symm

theorem pLift_eq_sup (M : S172X.S172Model S B G₀) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    {K' : Subgroup Ω} (hK'S : K' ≤ S) (hK' : Group.IsPerfect ↥K') {E : Subgroup G₀} {P : Subgroup Ω}
    (hPS : P ≤ S) (hPel : IsElemAbelian p P) (hPE : piImg M P = E) (hPcard : Nat.card P = Nat.card E)
    (hp : p.Prime)
    (hE : E = (E ⊓ piImg M K') ⊔ (E ⊓ Subgroup.centralizer (piImg M K' : Set G₀))) :
    P = (P ⊓ K') ⊔ (P ⊓ Subgroup.centralizer (K' : Set Ω)) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro u hu
  have hker := piImg_inf_ker_eq_bot M hPS hPE hPcard
  have hπu : M.π ⟨u, hPS hu⟩ ∈
      (E ⊓ piImg M K') ⊔ (E ⊓ Subgroup.centralizer (piImg M K' : Set G₀)) := by
    rw [← hE, ← hPE]
    exact Subgroup.mem_map_of_mem M.π hu
  have hEel : IsElemAbelian p E := hPE ▸ (hPel.subgroupOf S).map M.π
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_alt_iv_of_model_aux0
      (fun a ha b hb => hEel.comm (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hb).1) hπu
  have haP : a ∈ piImg M P := by rw [hPE]; exact ha.1
  have hbP : b ∈ piImg M P := by rw [hPE]; exact hb.1
  obtain ⟨u₁, hu₁, hu₁π⟩ := Subgroup.mem_map.1 haP
  obtain ⟨u₂, hu₂, hu₂π⟩ := Subgroup.mem_map.1 hbP
  have hprod : M.π ⟨u, hPS hu⟩ = M.π (u₁ * u₂) := by
    rw [← hab, ← hu₁π, ← hu₂π, map_mul]
  have hdiff : ⟨u, hPS hu⟩ * (u₁ * u₂)⁻¹ ∈ P.subgroupOf S ⊓ M.π.ker := by
    refine ⟨?_, ?_⟩
    · exact (P.subgroupOf S).mul_mem hu
        ((P.subgroupOf S).inv_mem ((P.subgroupOf S).mul_mem hu₁ hu₂))
    · exact MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hprod, mul_inv_cancel])
  have hone : ⟨u, hPS hu⟩ * (u₁ * u₂)⁻¹ = 1 := by
    have h := hdiff
    rw [hker] at h
    exact Subgroup.mem_bot.1 h
  have hueq : (⟨u, hPS hu⟩ : ↥S) = u₁ * u₂ := mul_inv_eq_one.1 hone
  have hu₁K : (u₁ : Ω) ∈ K' :=
    mem_of_piImg_of_pow_eq_one M hK'S hp hZ (by rw [hu₁π]; exact ha.2)
      (Subtype.ext (by simpa using hPel.2 (u₁ : Ω) hu₁))
  have hu₂C : (u₂ : Ω) ∈ Subgroup.centralizer (K' : Set Ω) :=
    exists_alt_iv_of_model_aux3 M hK'S hK' (by rw [hu₂π]; exact hb.2)
  have hueqΩ : (u : Ω) = (u₁ : Ω) * (u₂ : Ω) := by
    have := congrArg (Subtype.val) hueq
    simpa using this
  rw [hueqΩ]
  exact ((P ⊓ K') ⊔ (P ⊓ Subgroup.centralizer (K' : Set Ω))).mul_mem
    (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hu₁, hu₁K⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hu₂, hu₂C⟩))

theorem piImg_inf_S_le_range_β (M : S172X.S172Model S B G₀) :
    piImg M (B ⊓ S) ≤ M.β.range := by
  intro g hg
  obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.1 hg
  refine ⟨⟨(s : Ω), hs.1⟩, ?_⟩
  obtain ⟨s', c, hc, hb, hβ⟩ := M.split ⟨(s : Ω), hs.1⟩
  have hcS : c ∈ S := by
    have hceq : c = (s' : Ω)⁻¹ * (s : Ω) := by rw [hb]; group
    rw [hceq]
    exact S.mul_mem (S.inv_mem s'.2) hs.2
  have hcZ : (⟨c, hcS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro t
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc (t : Ω) t.2)
  have hπc : M.π ⟨c, hcS⟩ = 1 := by
    rw [← MonoidHom.mem_ker, M.ker_π]
    exact hcZ
  have hs_eq : s = s' * ⟨c, hcS⟩ := Subtype.ext hb
  have hπs : M.π s = M.π s' * M.π ⟨c, hcS⟩ := by rw [hs_eq, map_mul]
  rw [hβ, ← hsg, hπs, hπc, mul_one]

private lemma exists_alt_iv_of_model_aux6 {A Kbar : Subgroup G₀} {y : G₀}
    (hA : A = (A ⊓ Kbar) ⊔ (A ⊓ Subgroup.centralizer (Kbar : Set G₀)))
    (hyA : y ∈ Subgroup.centralizer (A : Set G₀))
    (hyK : y ∈ Subgroup.centralizer (Kbar : Set G₀)) :
    A ⊔ Subgroup.zpowers y =
      ((A ⊔ Subgroup.zpowers y) ⊓ Kbar) ⊔
        ((A ⊔ Subgroup.zpowers y) ⊓ Subgroup.centralizer (Kbar : Set G₀)) := by
  have hyK' : Subgroup.zpowers y ≤ Subgroup.centralizer (Kbar : Set G₀) :=
    Subgroup.zpowers_le.2 hyK
  apply le_antisymm
  · refine sup_le ?_ ?_
    · refine (le_of_eq hA).trans (sup_le ?_ ?_)
      · exact (le_inf (inf_le_left.trans le_sup_left) inf_le_right).trans le_sup_left
      · exact (le_inf (inf_le_left.trans le_sup_left) inf_le_right).trans le_sup_right
    · exact (le_inf le_sup_right hyK').trans le_sup_right
  · exact sup_le inf_le_left inf_le_left

private lemma exists_alt_iv_of_model_aux7 {x : Ω} {P' K U : Subgroup Ω}
    (hxS : x ∈ Subgroup.centralizer (S : Set Ω)) (hUS : U ≤ S) (hUK : U ≤ K)
    (hsplit : P' = (P' ⊓ K) ⊔ (P' ⊓ Subgroup.centralizer (K : Set Ω))) :
    Subgroup.zpowers x ⊔ P' =
      ((Subgroup.zpowers x ⊔ P') ⊓ K) ⊔
        ((Subgroup.zpowers x ⊔ P') ⊓ Subgroup.normalizer (U : Set Ω)) := by
  set B : Subgroup Ω := Subgroup.zpowers x ⊔ P' with hB
  set N : Subgroup Ω := Subgroup.normalizer (U : Set Ω) with hN
  have hC : Subgroup.centralizer (K : Set Ω) ≤ N := by
    rw [hN]
    exact (Subgroup.centralizer_le (show (U : Set Ω) ⊆ (K : Set Ω) from fun u hu => hUK hu)).trans
      (Subgroup.centralizer_le_normalizer (U : Set Ω))
  have hxN : Subgroup.zpowers x ≤ N := by
    rw [hN]
    exact (Subgroup.zpowers_le.2 hxS).trans
      ((Subgroup.centralizer_le (show (U : Set Ω) ⊆ (S : Set Ω) from fun u hu => hUS hu)).trans
        (Subgroup.centralizer_le_normalizer (U : Set Ω)))
  change B = (B ⊓ K) ⊔ (B ⊓ N)
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact (le_inf le_sup_left hxN).trans le_sup_right
    · refine (le_of_eq hsplit).trans (sup_le ?_ ?_)
      · exact (le_inf (inf_le_left.trans le_sup_right) inf_le_right).trans le_sup_left
      · exact (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans hC)).trans le_sup_right
  · exact sup_le inf_le_left inf_le_left

theorem isElemAbelian_zpowers_sup_of_le_S (hcfg : Cfg173 p S B N D K x) {P' : Subgroup Ω} (hP'S : P' ≤ S)
    (hP'el : IsElemAbelian p P') :
    IsElemAbelian p (Subgroup.zpowers x ⊔ P') := by
  have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ P', a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hxb : Commute x b := (Subgroup.mem_centralizer_iff.1 hxcent b (hP'S hb)).symm
    exact (hxb.zpow_left n).eq
  exact (isElemAbelian_zpowers (hcfg.elem.2 x hcfg.mem)).sup_of_commute hP'el hcomm

theorem exists_alt_iv_of_model (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {d : G₀} (hd : piImg M K = stdLayer d)
    (hext : StdExtends p M.β.range d) :
    ∃ B' U : Subgroup Ω, IsElemAbelian p B' ∧ B' ≤ S ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ K ∧
      B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Ω)) := by
  obtain ⟨y, hyA, hyK, hyp, hyA'⟩ := hext.2
  have hEab : IsElemAbelian p (M.β.range ⊔ Subgroup.zpowers y) :=
    (M.isElemAbelian_range_β hcfg.elem).sup_of_commute (isElemAbelian_zpowers hyp)
      (fun a ha b hb => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        have hay : Commute a y := Subgroup.mem_centralizer_iff.1 hyA a ha
        exact (hay.zpow_right n).eq)
  obtain ⟨P', hP'S, hP'el, hP'E, hP'card, hP'max⟩ := exists_pLift hcfg M hZ hEab
  have hBS : B ⊓ S ≤ P' := by
    refine hP'max (B ⊓ S) inf_le_right (hcfg.elem.mono inf_le_left).isPGroup ?_
    exact (piImg_inf_S_le_range_β M).trans le_sup_left
  obtain ⟨U, hUK, hU1, hU2⟩ := exists_two_subgroup_le_K hcfg
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  have hUS : U ≤ S := hUK.trans hKS
  have hEsplit : M.β.range ⊔ Subgroup.zpowers y =
      ((M.β.range ⊔ Subgroup.zpowers y) ⊓ piImg M K) ⊔
        ((M.β.range ⊔ Subgroup.zpowers y) ⊓ Subgroup.centralizer (piImg M K : Set G₀)) := by
    rw [hd]
    exact exists_alt_iv_of_model_aux6 hext.1 hyA hyK
  have hP'split : P' = (P' ⊓ K) ⊔ (P' ⊓ Subgroup.centralizer (K : Set Ω)) :=
    pLift_eq_sup M hZ hKS (isPerfect_K hcfg) hP'S hP'el hP'E hP'card
      hcfg.prime hEsplit
  refine ⟨Subgroup.zpowers x ⊔ P', U, ?_, ?_, ?_, ?_, hU1, hU2, hUK, ?_⟩
  · exact isElemAbelian_zpowers_sup_of_le_S hcfg hP'S hP'el
  · exact sup_le ((Subgroup.zpowers_le.2 hcfg.mem).trans le_sup_right) (hP'S.trans le_sup_left)
  · rw [eq_zpowers_sup_inf hcfg M hZ]
    exact sup_le le_sup_left (hBS.trans le_sup_right)
  · intro hB'
    have hP'B : P' ≤ B := by rw [hB']; exact le_sup_right
    have hP'BS : P' ≤ B ⊓ S := le_inf hP'B hP'S
    have hmono : piImg M P' ≤ piImg M (B ⊓ S) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono S hP'BS)
    have hyE : y ∈ piImg M P' := by
      rw [hP'E]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    exact hyA' ((hmono.trans (piImg_inf_S_le_range_β M)) hyE)
  · exact exists_alt_iv_of_model_aux7 ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)) hUS hUK hP'split

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
