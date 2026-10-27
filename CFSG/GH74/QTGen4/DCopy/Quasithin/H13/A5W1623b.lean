module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.Quasithin.H13.A5W1622s
public import CFSG.Quasithin.H13.A5W1622u
public import CFSG.Quasithin.H13.A5W1623a
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2B

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.A5Model
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap
  mem_normalizer_perfectCore exists_inducedAut liftCore_perfect)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_slHom_plus_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hGA : GriessAllModelsStatement)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLv : S.Lv ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {m : ℕ} (hm4 : 4 ≤ m) (hm5 : m ≤ 5)
    (e : ↥(S.plus K) ≃* SpecialLinearGroup (Fin m) (ZMod 2)) :
    ∃ α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥K ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Ln2P.card_zmod_two
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) := hKH.trans hR.2.1
  set φ := InternalSec.autOnHom hKW with hφ
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hKW
  let e' : ↥(autOn K (S.WK K)) ≃* SpecialLinearGroup (Fin m) (ZMod 2) := e

  have hHK : S.HK K ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hLv) hT
  have hOC : pCoreOf 2 K ≤ Subgroup.centralizer (S.WK K : Set G) := by
    refine hR.2.2.2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (fun g hg => C1.mem_normalizer_blockQ (hHK hg)) fun d hd => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h1]
    exact Subgroup.one_mem _
  have hNK : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro q hq
    rw [InternalSec.mem_ker_autOnHom]
    have hq' : q ∈ CFSG.Open.pCore 2 ↥K := by rw [← CFSG.pCore_eq_open]; exact hq
    exact hOC ⟨q, hq', rfl⟩
  let α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2) := e'.toMonoidHom.comp φ
  have hαφ : ∀ k, α k = 1 ↔ φ k = 1 := fun k => MulEquiv.map_eq_one_iff e'
  have hαs : Function.Surjective α := e'.surjective.comp hφs

  have hKN : φ.ker ≤ CFSG.pCore 2 ↥K := by
    set N := CFSG.pCore 2 ↥K with hN
    set Kφ := φ.ker with hKφ
    have hNn : N.Normal := CFSG.pCore_normal
    have : Group.IsPerfect (↥K ⧸ N) := hq.1
    let e₂ : ↥(autOn K (S.WK K)) ≃* StatedProj (StatedSL m (ZMod 2)) :=
      e'.trans (slEquivStatedProj hK2 m)
    let q : ↥K ⧸ N →* StatedProj (StatedSL m (ZMod 2)) :=
      e₂.toMonoidHom.comp (QuotientGroup.lift N φ hNK)
    have hqmk : ∀ k : ↥K, q (k : ↥K ⧸ N) = e₂ (φ k) := fun k => rfl
    have hqs : Function.Surjective q := by
      intro y
      obtain ⟨k, hk⟩ := hφs (e₂.symm y)
      exact ⟨k, by rw [hqmk, hk, MulEquiv.apply_symm_apply]⟩
    have hker : ∀ k : ↥K, q (k : ↥K ⧸ N) = 1 ↔ k ∈ Kφ := fun k => by
      rw [hqmk]
      exact MulEquiv.map_eq_one_iff e₂
    have hqn : q.ker.Normal := MonoidHom.normal_ker q
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq q.ker with hc | htop
    ·
      have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hqs hc
      have hcard : Nat.card ↥q.ker ∣ 2 := by
        have h1 := Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier
          (StatedProj (StatedSL m (ZMod 2)))) (RankThree.PerfectCover.hopfLift q hqs hc)
        rw [hmap] at h1
        exact h1.trans (Ln2.card_hopfMultiplier_dvd_two hGA hK2 hm4 hm5)
      have hp : IsPGroup 2 ↥q.ker := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h1
        · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
        · exact IsPGroup.of_card (n := 1) (by rw [h1, pow_one])
      have hK2' : IsPGroup 2 ↥Kφ := by
        rintro ⟨k, hk⟩
        obtain ⟨a, ha⟩ := hp ⟨(k : ↥K ⧸ N), (hker k).mpr hk⟩
        have ha' : ((k ^ 2 ^ a : ↥K) : ↥K ⧸ N) = 1 := by
          have := congrArg Subtype.val ha
          simpa using this
        have hkN : k ^ 2 ^ a ∈ N := (QuotientGroup.eq_one_iff _).mp ha'
        obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hkN⟩
        refine ⟨a + b, Subtype.ext ?_⟩
        have hb' : (k ^ 2 ^ a) ^ 2 ^ b = 1 := by
          have := congrArg Subtype.val hb
          simpa using this
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [pow_add, pow_mul, hb']
      exact le_sSup ⟨MonoidHom.normal_ker φ, hK2'⟩
    · exfalso
      have htriv : ∀ k : ↥K, φ k = 1 := by
        intro k
        have hk : (k : ↥K ⧸ N) ∈ q.ker := htop ▸ Subgroup.mem_top _
        exact (hker k).mp hk
      obtain ⟨a, b, hab⟩ := sl_nonabelian_of_card_two hK2 (m := m) (by omega)
      obtain ⟨x, rfl⟩ := hαs a
      obtain ⟨y, rfl⟩ := hαs b
      apply hab
      have hx : α x = 1 := (hαφ x).mpr (htriv x)
      have hy : α y = 1 := (hαφ y).mpr (htriv y)
      rw [hx, hy]
  refine ⟨α, hαs, ?_, fun k => ?_⟩
  · ext k
    rw [MonoidHom.mem_ker, hαφ, ← MonoidHom.mem_ker]
    exact ⟨fun hk => hKN hk, fun hk => hNK hk⟩
  · rw [hαφ, ← MonoidHom.mem_ker, InternalSec.mem_ker_autOnHom]

theorem eq_parabolic_of_sl_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K : Subgroup G} (hLvK : S.Lv ≤ K) {m : ℕ} (hm : 3 ≤ m)
    {α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2)}
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular m (ZMod 2)) :
    ∃ j, 1 ≤ j ∧ j < m ∧ ((S.Lv ⊔ (S.Tv ⊓ K)).subgroupOf K).map α =
      flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := S.Lv ⊔ (S.Tv ⊓ K) with hXdef
  set P := (X.subgroupOf K).map α with hPdef
  have hXK : X ≤ K := sup_le hLvK inf_le_right
  have hTvK : S.Tv ⊓ K ≤ Subgroup.normalizer (S.Lv : Set G) :=
    inf_le_left.trans S.Tv_le_normalizer_Lv
  have hUP : unitriangular m (ZMod 2) ≤ P := by
    rw [← hmapU]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  have hsylU : IsSylowTwoOf (unitriangular m (ZMod 2)) ⊤ :=
    SzN2.isSylowTwoOf_unitriangular (by omega)

  have hT2 : IsPGroup 2 ↥(S.Tv ⊓ K) := (S.isSylowTwoOf_Tv_F4 h1222 h517).2.1.to_le inf_le_left
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hT2
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp S.isPGroup_LvQ
  have hLv : Nat.card S.Lv = S.LvQ.relIndex S.Lv * 2 ^ a := by
    rw [← ha, ← Subgroup.relIndex_mul_card (H := S.LvQ) (K := S.Lv),
      inf_eq_left.mpr S.LvQ_le_Lv]
  have hX : Nat.card X ∣ S.LvQ.relIndex S.Lv * 2 ^ (a + b) := by
    have h1 := Ln2P.card_sup_dvd_mul S.Lv (S.Tv ⊓ K) hTvK
    rw [hLv, hb, mul_assoc, ← pow_add] at h1
    exact h1
  have hPc : Nat.card P ∣ Nat.card X := by
    have h1 := Subgroup.card_map_dvd (H := X.subgroupOf K) α
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv] at h1
  have hodd : ¬ 2 ∣ (unitriangular m (ZMod 2)).relIndex P := fun h2 => by
    apply hsylU.2.2
    show 2 ∣ (unitriangular m (ZMod 2)).relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hUP]
    exact Dvd.dvd.mul_right h2 _
  have hidx : (unitriangular m (ZMod 2)).relIndex P ∣ S.LvQ.relIndex S.Lv := by
    have h1 : (unitriangular m (ZMod 2)).relIndex P ∣ Nat.card P := by
      rw [← Subgroup.relIndex_mul_card (H := unitriangular m (ZMod 2)) (K := P)]
      exact Dvd.intro _ rfl
    have h2 := h1.trans (hPc.trans hX)
    have hco : Nat.Coprime ((unitriangular m (ZMod 2)).relIndex P) (2 ^ (a + b)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    exact hco.dvd_of_dvd_mul_right h2
  have hpos : 0 < S.LvQ.relIndex S.Lv := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h3 : (unitriangular m (ZMod 2)).relIndex P ≤ 3 :=
    (Nat.le_of_dvd hpos hidx).trans S.relIndex_LvQ_le
  rcases eq_or_eq_parabolic hUP h3 with hPU | ⟨j, ⟨hj, hjm, hPj⟩, -⟩
  ·
    exfalso
    apply S.not_Lv_le_centralizer_z
    have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
    refine le_trans ?_ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzW))
    show oTwoRes (L ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤ _
    rw [oTwoRes, Subgroup.closure_le]
    rintro x ⟨hxX, m', hm', hxm⟩
    have hxLv : x ∈ S.Lv := Subgroup.subset_closure ⟨hxX, m', hm', hxm⟩
    have hxK : x ∈ K := hLvK hxLv
    have hxP : α ⟨x, hxK⟩ ∈ unitriangular m (ZMod 2) := by
      rw [← hPU]
      exact ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hxLv), rfl⟩
    obtain ⟨e, he⟩ := hsylU.2.1 ⟨_, hxP⟩
    have h1 : α ⟨x, hxK⟩ ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have h2 : α ⟨x, hxK⟩ ^ m' = 1 := by
      rw [← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ m' = 1 := Subtype.ext (by simpa using hxm)
      rw [this, map_one]
    have h3 : α ⟨x, hxK⟩ = 1 := by
      have h5 := Ln2P.mem_of_pow_two_pow_mem (N := ⊥) hm' h2 (by rw [h1]; exact Subgroup.one_mem _)
      exact Subgroup.mem_bot.mp h5
    exact (hαC ⟨x, hxK⟩).mp h3
  · exact ⟨j, hj, hjm, hPj⟩

theorem false_of_sl_inner_F4
    (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4) (hres : Lem13622Case4Z0_F4)
    (hH : S.Hyp1367) {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLvK : S.Lv ≤ K) {m : ℕ} (hm4 : 4 ≤ m)
    (hm5 : m ≤ 5) {α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2)}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥K) {j : ℕ} (hj : 1 ≤ j)
    (hjm : j < m) (hP : ((S.Lv ⊔ (S.Tv ⊓ K)).subgroupOf K).map α =
      flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}))
    (hinner : ∀ t ∈ S.Tv, ∃ u ∈ unitriangular m (ZMod 2), ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
      α ⟨t * l * t⁻¹, h⟩ = u * α l * u⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Ln2P.card_zmod_two
  have hF := hH.hF

  obtain ⟨a, ha3, haj, hja, hJ, hno, hJa, hJb⟩ := Ln2P.exists_block (by omega) hj hjm
  generalize hJdef : Set.Icc 1 (m - 1) \ {a + 1, a + 2} = J at hJ hno hJa hJb
  set Q := flagStabilizer m (ZMod 2) J with hQdef
  set K₁ := liftCore α Q with hK₁def
  obtain ⟨f, hf, hfk⟩ := Ln2.exists_hom_big hK2 hm5 hαs hαk ha3 le_rfl hJa hJb hno
  have hs3 : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    sl_isSimple_of_card_two hK2 le_rfl

  have hTP : S.Tv ≤ Subgroup.normalizer (liftPre α Q : Set G) := by
    intro t ht
    obtain ⟨u, hu, hcu⟩ := hinner t ht
    have huQ : u ∈ Q := unitriangular_le_flagStabilizer J hu
    apply L3316.mem_normalizer_of_map_le
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    have hlK : t * (l : G) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hT ht) l).mp l.2
    refine ⟨⟨t * l * t⁻¹, hlK⟩, ?_, rfl⟩
    show α ⟨t * l * t⁻¹, hlK⟩ ∈ Q
    rw [hcu l hlK]
    exact Q.mul_mem (Q.mul_mem huQ hl) (Q.inv_mem huQ)
  have hTK₁ : S.Tv ≤ Subgroup.normalizer (K₁ : Set G) := fun t ht =>
    mem_normalizer_perfectCore (hTP ht)
  have hK₁K : K₁ ≤ K := liftCore_le α Q
  have hK₁G : K₁ ≤ Subgroup.centralizer ({S.v12} : Set G) := hK₁K.trans hKG
  have hK₁1 : K₁ ≠ ⊥ := by
    intro h
    have : Nontrivial (SpecialLinearGroup (Fin 3) (ZMod 2)) := hs3.toNontrivial
    obtain ⟨c, d, hcd⟩ := exists_pair_ne (SpecialLinearGroup (Fin 3) (ZMod 2))
    obtain ⟨x, rfl⟩ := hf c
    obtain ⟨y, rfl⟩ := hf d
    apply hcd
    have hx : (x : G) ∈ (⊥ : Subgroup G) := by rw [← h]; exact x.2
    have hy : (y : G) ∈ (⊥ : Subgroup G) := by rw [← h]; exact y.2
    rw [Subgroup.mem_bot] at hx hy
    have hxy : x = y := Subtype.ext (by rw [hx, hy])
    rw [hxy]
  have hK₁c : K₁ ∈ cComp (K₁ ⊔ S.Tv) :=
    Sec1216Lv.mem_cComp_of_hom (X := K₁) (T := S.Tv) (liftCore_perfect α Q) hK₁1 hTK₁ f hf hfk
  have hK₁L : K₁ ∈ lFamily S.Tv := hK₁c

  have hLvK₁ : S.Lv ≤ K₁ := by
    show oTwoRes (L ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤ K₁
    rw [oTwoRes, Subgroup.closure_le]
    rintro x ⟨hxX, m', hm', hxm⟩
    have hxLv : x ∈ S.Lv := Subgroup.subset_closure ⟨hxX, m', hm', hxm⟩
    have hxK : x ∈ K := hLvK hxLv
    set y : ↥K := ⟨x, hxK⟩ with hy
    have hym : y ^ m' = 1 := Subtype.ext (by simpa using hxm)
    have hyP : α y ∈ flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}) := by
      rw [← hP]
      exact ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hxLv), rfl⟩
    have hyQ : α y ∈ perfectCore Q :=
      Ln2P.mem_perfectCore_of_odd ha3 haj hja hJ hno hyP hm' (by rw [← map_pow, hym, map_one])
    rw [← map_perfectCore_comap hαs Q] at hyQ
    obtain ⟨w, hw, hwy⟩ := hyQ
    have hn1 : α (w⁻¹ * y) = 1 := by rw [map_mul, map_inv, hwy, inv_mul_cancel]
    have hn : w⁻¹ * y ∈ CFSG.pCore 2 ↥K := by
      rw [← hαk, MonoidHom.mem_ker]
      exact hn1
    have hnH : w⁻¹ * y ∈ Q.comap α := by
      rw [Subgroup.mem_comap, hn1]
      exact Q.one_mem
    have hnN : w⁻¹ * y ∈ Subgroup.normalizer (perfectCore (Q.comap α) : Set ↥K) :=
      mem_normalizer_perfectCore (Subgroup.le_normalizer hnH)
    obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hn⟩
    have hne : (w⁻¹ * y) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have h1 := Ln2P.mul_pow_mul_inv_mem hw hnN (2 ^ e)
    rw [hne, inv_one, mul_one, mul_inv_cancel_left] at h1
    have h2 := Ln2P.mem_of_pow_two_pow_mem hm' hym h1
    rw [hK₁def, liftCore_eq]
    exact ⟨y, h2, rfl⟩
  have hz₁ : ¬ K₁ ≤ Subgroup.centralizer ({S.z} : Set G) := fun h =>
    S.not_Lv_le_centralizer_z (hLvK₁.trans h)
  have hchar₁ : CharTwo (K₁ ⊔ S.Tv) :=
    C1GN.charTwo_of_le hF (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right (sup_le hK₁G S.Tv_le_Gv)

  obtain ⟨e₁⟩ := L3312.modO2_equiv_of_surjective f hf hfk
  let e₂ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq Ln2P.pCore_sl3_two).trans
      QuotientGroup.quotientBot)
  have hl : IsPSL 3 2 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨ IsAlt 6 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      IsPSU 3 3 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) :=
    Or.inl (L3316.isPSL3_of_equiv le_rfl (by rw [hK2, pow_one])
      (e₂.trans (slEquivStatedProj hK2 3)))
  have hRk₁ := SBc11.isRankTwoLie2Derived_of_list
    (isList_of_mulEquiv (quotCenterEquivOfEqBot (SBc11.center_eq_bot_of_list hl)).symm hl)
  have h64₁ : ¬ 64 ∣ Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    rw [Nat.card_congr e₂.toEquiv, Ln2P.card_sl3_two]
    norm_num
  exact S.false_of_msPair_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 h132 h134 hres hH
    ⟨hK₁G, hK₁L, hTK₁, hz₁, hLvK₁, hchar₁⟩ hRk₁ h64₁

end Setting

end CFSG.Quasithin.H13.A5
