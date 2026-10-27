module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec81b
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.Sec84a
import CFSG.Goldschmidt.Steps.Sec8Comp
import CFSG.Goldschmidt.Steps.G52
import CFSG.Walter.Bender1970.S4.Rank
import CFSG.Walter.Bender1970.S38.OddCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_conj_le [Finite G] {V : Subgroup G} {b : G}
    (h : ∀ v ∈ V, b⁻¹ * v * b ∈ V) : b ∈ Subgroup.normalizer (V : Set G) := by
  have hle : conjSub b V ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using h v hv
  have heq : conjSub b V = V := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  rw [← mem_conjSub, heq]

omit [Finite G] in
theorem comm_of_inv {X : Subgroup G} {b : G} (h : ∀ x ∈ X, b⁻¹ * x * b = x⁻¹) {x y : G}
    (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x := by
  have hxy := h _ (X.mul_mem hx hy)
  have e : b⁻¹ * (x * y) * b = (b⁻¹ * x * b) * (b⁻¹ * y * b) := by group
  rw [e, h x hx, h y hy] at hxy
  calc x * y = ((x * y)⁻¹)⁻¹ := by rw [inv_inv]
    _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [hxy]
    _ = y * x := by group

theorem le_normalizer_of_le_qCoreOf (h83 : S_G83) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) {p : ℕ} (hp : p.Prime) {V : Subgroup G} (hVO : V ≤ qCoreOf H p) :
    A ≤ Subgroup.normalizer (V : Set G) := fun b hb => by
  by_cases hb1 : b = 1
  · rw [hb1]
    exact Subgroup.one_mem _
  refine mem_normalizer_of_conj_le fun v hv => ?_
  rcases (h83 G S A hset h4 a ha ha1 H hH).1 b hb hb1 p hp with h | h
  · rw [h v (hVO hv)]
    exact hv
  · rw [h v (hVO hv)]
    exact V.inv_mem hv

theorem qCoreOf_inf_centralizer_ne_bot {H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h1 : qCoreOf H p ≠ ⊥) :
    qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p (qCoreOf H p) := qCoreOf_isPGroup H p
  have : Nontrivial (qCoreOf H p) := (Subgroup.nontrivial_iff_ne_bot _).mpr h1
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hP.bot_lt_center).ne'
  intro hbot
  apply hz1
  have hzZ : ((z : qCoreOf H p) : G) ∈
      qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) :=
    ⟨(z : qCoreOf H p).2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)⟩
  rw [hbot, Subgroup.mem_bot] at hzZ
  exact Subtype.ext (Subtype.ext hzZ)

theorem exists_conj_of_mem_normalizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {M : Subgroup G} {n : G} (hnM : n ∈ M) (hn : n ∈ Subgroup.normalizer (A : Set G))
    (hnc : n ∉ Subgroup.centralizer (A : Set G)) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) : ∃ m ∈ M, m * a * m⁻¹ = b := by
  obtain ⟨hca, hcc⟩ := conj_conj_eq_mul hset h4 hn hnc ha ha1
  rcases mem_four hset.elem h4 ha (conj_mem hn ha) hb ha1 (conj_ne_one ha1) (Ne.symm hca) with
    h | h | h | h
  · exact absurd h hb1
  · exact ⟨1, M.one_mem, by rw [h]; group⟩
  · exact ⟨n, hnM, h.symm⟩
  · refine ⟨n * n, M.mul_mem hnM hnM, ?_⟩
    rw [h, ← hcc]
    group

theorem centralizer_mem_benderM (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a b : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) (hHa : H = Subgroup.centralizer ({a} : Set G)) :
    Subgroup.centralizer ({b} : Set G) ∈ Walter.benderM b := by
  obtain ⟨n, -, rfl⟩ := exists_conj_eq hset h4 ha hb ha1 hb1
  have := Walter.map_conj_mem_benderM n hH
  rwa [hHa, Walter.map_conj_centralizer_singleton] at this

omit [Finite G] in
theorem oddCoreOf_eq_gw (H : Subgroup G) : oddCoreOf H = GorensteinWalter.oddCoreOf H := by
  rw [oddCoreOf, goldschmidtOddCore_eq_pPrimeCore]
  rfl

omit [Finite G] in
theorem oddCoreOf_map_conj' (H : Subgroup G) (g : G) :
    oddCoreOf (H.map (MulAut.conj g).toMonoidHom) =
      (oddCoreOf H).map (MulAut.conj g).toMonoidHom := by
  rw [oddCoreOf_eq_gw, oddCoreOf_eq_gw, Walter.oddCoreOf_map_conj]

theorem false_of_oddCoreOf_le (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a)
    (hHa : H = Subgroup.centralizer ({a} : Set G)) {M : Subgroup G} (hMtop : M ≠ ⊤)
    (hOM : oddCoreOf H ≤ M) {n : G} (hnM : n ∈ M) (hn : n ∈ Subgroup.normalizer (A : Set G))
    (hnc : n ∉ Subgroup.centralizer (A : Set G)) : False := by
  have := hset.isSimpleGroup
  set W := ⨆ b : {b : G // b ∈ A ∧ b ≠ 1}, oddCoreOf (Subgroup.centralizer ({b.1} : Set G))
    with hW
  have hOb : ∀ b ∈ A, b ≠ 1 → oddCoreOf (Subgroup.centralizer ({b} : Set G)) ≤ M := by
    intro b hb hb1
    obtain ⟨m, hm, rfl⟩ := exists_conj_of_mem_normalizer hset h4 hnM hn hnc ha ha1 hb hb1
    rw [← Walter.map_conj_centralizer_singleton, oddCoreOf_map_conj', ← hHa]
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hOM hy)) (M.inv_mem hm)
  have hWM : W ≤ M := iSup_le fun b => hOb b.1 b.2.1 b.2.2
  have hW1 : W ≠ ⊥ := by
    intro hbot
    apply commutator_ne_bot hset h4 ha ha1 hH
    have hle : oddCoreOf H ≤ W := hHa ▸ le_iSup (fun b : {b : G // b ∈ A ∧ b ≠ 1} =>
      oddCoreOf (Subgroup.centralizer ({b.1} : Set G))) ⟨a, ha, ha1⟩
    rw [hbot, le_bot_iff] at hle
    rw [hle, Subgroup.commutator_bot_right]
  have hNW : Subgroup.normalizer (W : Set G) ≠ ⊤ := by
    intro htop
    have : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW1 h
    · exact hMtop (top_le_iff.mp (h ▸ hWM))
  have hCW : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hW, Subgroup.map_iSup]
    refine iSup_congr fun b => ?_
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_oddCoreOf _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr b.2.1) hc))
  refine false_of_centralizer_le hset hNW fun b hb hb1 => ?_
  have hHb := centralizer_mem_benderM hset h4 ha ha1 hb hb1 hH hHa
  rw [(eq_oddCoreOf_sup hset h4 hb hb1 hHb).2]
  refine sup_le ((le_iSup (fun b : {b : G // b ∈ A ∧ b ≠ 1} =>
    oddCoreOf (Subgroup.centralizer ({b.1} : Set G))) ⟨b, hb, hb1⟩).trans
      Subgroup.le_normalizer) hCW

theorem not_mem_fstar (h64 : S_G64) (h31 : S_G31) (h37 : S_G37) (h83 : S_G83)
    (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {H : Subgroup G} (hH : H ∈ Walter.benderM a) {V : Subgroup G}
    (hVF : V ≤ CFSG.fittingSubgroupOf H) (hVp : (Nat.card V).Prime) {M : Subgroup G}
    (hM : IsCoatom M) (hVM : Subgroup.normalizer (V : Set G) ≤ M) (hMH : M ≠ H) :
    a ∉ generalizedFittingSubgroupOf M := by
  have hsimple := hset.isSimpleGroup
  set p := Nat.card V with hpdef
  have : Fact p.Prime := ⟨hVp⟩
  have hVpg : IsPGroup p V := IsPGroup.of_card (n := 1) (by rw [pow_one])
  have hV1 : V ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hpdef
    exact Nat.not_prime_one (hpdef ▸ hVp)
  obtain ⟨ha2H, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have hVO : V ≤ qCoreOf H p := Walter.le_qCoreOf_of_le_fittingSubgroupOf hVp hVF hVpg
  have hAM : A ≤ M := (le_normalizer_of_le_qCoreOf h83 hset h4 ha ha1 hH hVp hVO).trans hVM
  have hS := sstar_of_le hset hM.1 hAM
  have hHco := Walter.isCoatom_of_mem_benderM hH
  have hHM : ¬ H ≤ M := fun hle => hMH ((hHco.le_iff.mp hle).resolve_left hM.1)
  intro haF
  have haFM : a ∉ CFSG.fittingSubgroupOf M := fun h => hMH (eq_of_le_centralizer h64 hset h4
    ha ha1 hH hVp hVO hM hVM haF (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Walter.fittingSubgroupOf_le_centralizer_layer M h) e he)))
  obtain ⟨L, hL, haL⟩ := exists_component_of_not_mem_fitting haF haFM
  have hLQ := isComponentOf_normalClosureIn hL (le_normalClosureIn hAM ha) haL
  have hAL := le_of_isComponentOf h31 hS hset.elem h4 hLQ
  by_cases hp2 : p = 2
  ·
    have hOV : oddCoreOf H ≤ Subgroup.centralizer (V : Set G) := by
      intro y hy
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hv2 : v ∈ qCoreOf H 2 := hp2 ▸ hVO hv
      have hc1 : y * v * y⁻¹ * v⁻¹ ∈ oddCoreOf H := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf H (hVF.trans
          (fittingSubgroupOf_le H) hv)) y⁻¹).mp (Subgroup.inv_mem _ hy)
        simpa [mul_assoc] using Subgroup.mul_mem _ hy this
      have hc2 : y * v * y⁻¹ * v⁻¹ ∈ qCoreOf H 2 :=
        Subgroup.mul_mem _ ((qCoreOf_normal_in H 2).2 y (oddCoreOf_le H hy) v hv2)
          (Subgroup.inv_mem _ hv2)
      obtain ⟨k, hk⟩ := qCoreOf_isPGroup H 2 ⟨_, hc2⟩
      have h1 := eq_one_of_pow_two_of_odd (odd_card_oddCoreOf H) hc1 (k := k)
        (by simpa using congrArg Subtype.val hk)
      calc v * y = (y * v * y⁻¹ * v⁻¹)⁻¹ * (y * v) := by group
        _ = y * v := by rw [h1, inv_one, one_mul]
    have hOM : oddCoreOf H ≤ M := hOV.trans ((Subgroup.centralizer_le_normalizer _).trans hVM)
    obtain ⟨n, hnM, hn, hnc⟩ := exists_mem_normalizer_of_isComponentOf h31 hset h4 hS hLQ
    exact false_of_oddCoreOf_le hset h4 ha ha1 hH hHa hM.1 hOM hnM hn hnc
  have hodd : Odd (Nat.card (qCoreOf H p)) := by
    obtain ⟨k, hk⟩ := (qCoreOf_isPGroup H p).exists_card_eq
    rw [hk]
    exact (hVp.odd_of_ne_two hp2).pow
  have hXp := qCoreOf_isPGroup H p
  have hXeq := G52.eq_componentLayerOf_sup_of_isPGroup hVp hXp hodd
  have hOFX : oddCoreOf (CFSG.fittingSubgroupOf (qCoreOf H p)) = qCoreOf H p := by
    rw [Walter.fittingSubgroupOf_eq_self_of_isNilpotent hXp.isNilpotent,
      G52.oddCoreOf_eq_self_of_odd hodd]
  have hXH : qCoreOf H p ≤ H := qCoreOf_le H p
  have hHX : H ≤ Subgroup.normalizer (qCoreOf H p : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hX1 : qCoreOf H p ≠ ⊥ := fun h => hV1 (le_bot_iff.mp (h ▸ hVO))
  obtain ⟨n, hn, hnc⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hba, -⟩ := conj_conj_eq_mul hset h4 hn hnc ha ha1
  have ha₁ : n * a * n⁻¹ ∈ A := conj_mem hn ha
  have ha₁1 : n * a * n⁻¹ ≠ 1 := conj_ne_one ha1
  have hodd' : ∀ x ∈ qCoreOf H p, x * x = 1 → x = 1 := fun x hx hx2 => by
    obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
    exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left k
      ((Nat.coprime_primes hVp Nat.prime_two).mpr hp2))).mp
      ⟨by simpa using congrArg Subtype.val hk, by rw [sq]; exact hx2⟩
  rcases (h83 G S A hset h4 a ha ha1 H hH).1 _ ha₁ ha₁1 p hVp with hcen | hinv
  ·
    have hXA : qCoreOf H p ≤ Subgroup.centralizer (A : Set G) := fun x hx =>
      mem_centralizer_of_mem_two hset h4 ha ha₁ ha1 ha₁1 (Ne.symm hba) (hHa ▸ hXH hx)
        (Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc x * (n * a * n⁻¹) = (n * a * n⁻¹) * ((n * a * n⁻¹)⁻¹ * x * (n * a * n⁻¹)) := by
                group
            _ = (n * a * n⁻¹) * x := by rw [hcen x hx]))
    set Z := qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf H p : Set G) with hZ
    have hZ1 := qCoreOf_inf_centralizer_ne_bot hVp hX1
    have hZM : Z ≤ M := fun z hz =>
      hVM (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hVO hz.2))
    have hZH : Z ≤ H := inf_le_left.trans hXH
    have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := fun h hh =>
      mem_normalizer_inf (hHX hh) (normalizer_le_normalizer_centralizer _ (hHX hh))
    have hZn : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
      fun y hy => hHZ (hHa ▸ hy.2)
    have hZp : IsPGroup p Z := hXp.to_le inf_le_left
    have hZodd : Odd (Nat.card Z) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hZeq := G52.eq_componentLayerOf_sup_of_isPGroup hVp hZp hZodd
    have hOFZ : oddCoreOf (CFSG.fittingSubgroupOf Z) = Z := by
      rw [Walter.fittingSubgroupOf_eq_self_of_isNilpotent hZp.isNilpotent,
        G52.oddCoreOf_eq_self_of_odd hZodd]
    obtain ⟨-, -, -, h3⟩ := h37 G M A hS hset.elem a ha ha1 Z hZM hZn hZeq
    rw [hOFZ] at h3
    have hZL : Z ≤ Subgroup.centralizer (L : Set G) := by
      by_contra hZL
      obtain ⟨-, -, -, -, hne⟩ := h3 L hL hZL
      exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_left.trans (Subgroup.le_centralizer_iff.mp (inf_le_left.trans hXA))))
    have hNZ : Subgroup.normalizer (Z : Set G) = H :=
      normalizer_eq_of_nontrivial_normal_in_coatom hsimple hHco hZH hZ1
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mpr hHZ)
    have hLH : L ≤ H := hNZ ▸
      (Subgroup.le_centralizer_iff.mp hZL).trans (Subgroup.centralizer_le_normalizer _)
    exact false_of_isComponentOf_le h31 hset h4 ha ha1 hH hS hLQ hLH
  ·
    set X := qCoreOf H p with hX
    have hXV : X ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun v hv => comm_of_inv hinv (hVO hv) hx
    have hXM : X ≤ M := hXV.trans ((Subgroup.centralizer_le_normalizer _).trans hVM)
    have hXn : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
      fun y hy => hHX (hHa ▸ hy.2)
    obtain ⟨-, -, -, h3⟩ := h37 G M A hS hset.elem a ha ha1 X hXM hXn hXeq
    rw [hOFX] at h3
    have ha₁L : n * a * n⁻¹ ∈ L := hAL ha₁
    have hXC : X ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      refine eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hodd' z hz.1 ?_)
      have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ ha₁L
      have hi := hinv z hz.1
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul] at hi
      calc z * z = z * z⁻¹ := by rw [← hi]
        _ = 1 := mul_inv_cancel z
    have hXL : ¬ X ≤ Subgroup.centralizer (L : Set G) := fun h =>
      hX1 (by rw [← inf_eq_left.mpr h]; exact hXC)
    obtain ⟨-, -, hXLC, ⟨y, hyX, hy⟩, -⟩ := h3 L hL hXL
    have hyN : y ∈ Subgroup.normalizer
        ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
      normalizer_le_normalizer_centralizer L ((sup_le Subgroup.le_normalizer
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))) (hXLC hyX))
    have hcyc : IsCyclic X := isCyclic_of_le_zpowers_sup hyN hy hXC
    apply hHM
    intro h hh
    apply hVM
    rw [← Walter.map_conj_eq_iff_mem_normalizer]
    have hVhX : V.map (MulAut.conj h).toMonoidHom ≤ X := by
      rintro _ ⟨v, hv, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hHX hh) v).mp (hVO hv)
    have hcard : Nat.card ((V.map (MulAut.conj h).toMonoidHom).subgroupOf X) =
        Nat.card (V.subgroupOf X) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVhX).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVO).toEquiv,
        Subgroup.card_map_of_injective (MulAut.conj h).injective]
    have heq := (IsCyclic.subgroup_eq_iff_card_eq (G := X)).mpr hcard
    have h1 := congrArg (Subgroup.map X.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hVhX, Subgroup.map_subgroupOf_eq_of_le hVO] at h1

end CFSG.Goldschmidt.Sec8
