module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_pPart_pow {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (g : X) :
    ∃ n e : ℕ, (g ^ n) ^ p ^ e = 1 ∧ ∀ {Y : Type*} [Group Y] (x : Y), x ^ orderOf g = 1 →
      (∃ k : ℕ, x ^ p ^ k = 1) → x ^ n = x := by
  obtain ⟨e, m, hpm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have hcop' : m.Coprime (p ^ e) :=
    Nat.Coprime.pow_right e ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm))
  refine ⟨m ^ Nat.totient (p ^ e), e, ?_, fun x hx ⟨k, hk⟩ => ?_⟩
  · have hφ : 0 < Nat.totient (p ^ e) := Nat.totient_pos.mpr (pow_pos hp.pos e)
    obtain ⟨j, hj⟩ : m ∣ m ^ Nat.totient (p ^ e) := dvd_pow_self m hφ.ne'
    rw [← pow_mul, hj, show m * j * p ^ e = (p ^ e * m) * j by ring, ← hm, pow_mul,
      pow_orderOf_eq_one, one_pow]
  ·
    have h1 : orderOf x ∣ p ^ e * m := hm ▸ orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk)
    have h2 : orderOf x ∣ p ^ e := by
      rw [hj] at h1 ⊢
      exact (Nat.Coprime.pow_left j
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)).dvd_of_dvd_mul_right h1
    have hmod : m ^ Nat.totient (p ^ e) ≡ 1 [MOD orderOf x] :=
      (Nat.ModEq.pow_totient hcop').of_dvd h2
    calc x ^ m ^ Nat.totient (p ^ e) = x ^ 1 := (pow_eq_pow_iff_modEq).mpr hmod
      _ = x := pow_one x

theorem exists_threeElt_of_mem_sup {X : Type*} [Group X] [Finite X] {L : Subgroup X} {u : X}
    (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set X)) (hu3 : u ^ 3 = 1) :
    ∃ l ∈ L, (∃ k : ℕ, l ^ 3 ^ k = 1) ∧ l⁻¹ * u ∈ Subgroup.centralizer (L : Set X) := by
  have hLC : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set X) : Set X) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hu
  obtain ⟨a, ha, c, hc, rfl⟩ := hu
  have hac : Commute a c := Subgroup.mem_centralizer_iff.mp hc a ha
  obtain ⟨n, e, hn, hfix⟩ := exists_pPart_pow Nat.prime_three ((a, c) : X × X)
  have hu' : (a * c) ^ n = a * c := by
    refine hfix (a * c) ?_ ⟨1, by simpa using hu3⟩
    have h1 := pow_orderOf_eq_one ((a, c) : X × X)
    rw [Prod.pow_mk, Prod.mk_eq_one] at h1
    rw [hac.mul_pow, h1.1, h1.2, one_mul]
  refine ⟨a ^ n, L.pow_mem ha n, ⟨e, ?_⟩, ?_⟩
  · have := congrArg Prod.fst hn
    simpa [← pow_mul] using this
  · have h2 : (a ^ n)⁻¹ * (a * c) = c ^ n := by
      conv_lhs => rw [← hu', hac.mul_pow]
      group
    rw [h2]
    exact Subgroup.pow_mem _ hc n

theorem exists_sylow_inf_of_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M R : Subgroup G} {z : G}
    (hB0 : ∃ Q : Sylow p (Subgroup.centralizer ({z} : Set G)),
      (Q : Subgroup (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype = R) (hRM : R ≤ M) :
    ∃ S : Sylow p ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R := by
  obtain ⟨Q, hQ⟩ := hB0
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hQ ▸ Subgroup.map_subtype_le _
  have hRp : IsPGroup p R := by rw [← hQ]; exact Q.isPGroup'.map _
  obtain ⟨S, hS⟩ :=
    (hRp.comap_subtype (K := M ⊓ Subgroup.centralizer ({z} : Set G))).exists_le_sylow
  refine ⟨S, ?_⟩
  have hRS : R ≤ (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype :=
    fun r hr => ⟨⟨r, hRM hr, hRC hr⟩, hS hr, rfl⟩
  have hS₁C : (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype ≤
      Subgroup.centralizer ({z} : Set G) := (Subgroup.map_subtype_le _).trans inf_le_right
  have hS₁p : IsPGroup p ((S : Subgroup _).map
      (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype) := S.isPGroup'.map _
  have hQle : (Q : Subgroup (Subgroup.centralizer ({z} : Set G))) ≤
      ((S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype).subgroupOf
        (Subgroup.centralizer ({z} : Set G)) := by
    intro q hq
    have hqR : (q : G) ∈ R := hQ ▸ ⟨q, hq, rfl⟩
    exact hRS hqR
  have heq := Q.is_maximal' hS₁p.comap_subtype hQle
  refine le_antisymm (fun x hx => ?_) hRS
  have hx' : (⟨x, hS₁C hx⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      (Q : Subgroup (Subgroup.centralizer ({z} : Set G))) := by
    rw [← heq]; exact hx
  exact hQ ▸ ⟨_, hx', rfl⟩

theorem exists_conj_mem_map_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Subgroup G} (S : Sylow p K) {g : G} (hg : g ∈ K) {k : ℕ} (hgk : g ^ p ^ k = 1) :
    ∃ y ∈ K, y * g * y⁻¹ ∈ (S : Subgroup K).map K.subtype := by
  have hZ : IsPGroup p (Subgroup.zpowers (⟨g, hg⟩ : K)) :=
    isPGroup_zpowers_of_pow_eq_one (k := k) (Subtype.ext (by simpa using hgk))
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K S' S
  have hmem : n * ⟨g, hg⟩ * n⁻¹ ∈ (S : Subgroup K) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers _))
  exact ⟨n, n.2, ⟨_, hmem, rfl⟩⟩

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1MSideAt.exists_rep_mem_R_at {M S R : Subgroup G} {z : G} (hzM : z ∈ M)
    (hz3 : z ^ 3 = 1) (hCz : M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (S : Set G))
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    {L : Subgroup G} (hL : IsWeakSBlock M S L)
    (hin : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ L' : Subgroup G, IsWeakSBlock M S L' ∧ ∃ r ∈ R, ∃ hrM : r ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩ ∈ barM M L' ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zM : M := ⟨z, hzM⟩ with hzMdef
  set zb := mk zM with hzb
  have hzM3 : zM ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by rw [hzb, ← map_pow, hzM3, map_one]
  obtain ⟨l, hlL, ⟨k, hlk⟩, hlc⟩ := exists_threeElt_of_mem_sup hin hzb3
  have hcl : l * (l⁻¹ * zb) = (l⁻¹ * zb) * l := Subgroup.mem_centralizer_iff.mp hlc l hlL
  have hlz : l ∈ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * zb = l * (l * (l⁻¹ * zb)) := by group
      _ = l * ((l⁻¹ * zb) * l) := by rw [hcl]
      _ = zb * l := by group
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have hzMp : IsPGroup 3 (Subgroup.zpowers zM) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hzM3)
  obtain ⟨g, hgC, hgl⟩ := exists_mem_centralizer_mk_eq Nat.prime_three (CFSG.pCore 2 ↥M) hcop
    hzMp hlz
  obtain ⟨n, e, hn, hfix⟩ := exists_pPart_pow Nat.prime_three g
  have hl1 : l ^ orderOf g = 1 := by rw [← hgl, ← map_pow, pow_orderOf_eq_one, map_one]
  have hg₃l : mk (g ^ n) = l := by rw [map_pow, hgl]; exact hfix l hl1 ⟨k, hlk⟩
  have hg₃C : g ^ n ∈ Subgroup.centralizer ({zM} : Set M) := Subgroup.pow_mem _ hgC n
  have hg₃K : ((g ^ n : M) : G) ∈ M ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine ⟨(g ^ n).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg₃C
    exact congrArg Subtype.val this
  have hg₃e : ((g ^ n : M) : G) ^ 3 ^ e = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨S₃, hS₃⟩ := hsyl
  obtain ⟨y, hyK, hyR⟩ := exists_conj_mem_map_sylow S₃ hg₃K hg₃e
  rw [hS₃] at hyR
  have hyM : y ∈ M := hyK.1
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyK.2
  have hyS : y ∈ Subgroup.normalizer (S : Set G) := hCz hyK
  set yM : M := ⟨y, hyM⟩ with hyMdef
  set yb := mk yM with hyb
  have hybz : yb * zb = zb * yb := by
    rw [hyb, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyz
  refine ⟨L.map (MulAut.conj y).toMonoidHom, hL.map_conj hyM hyS, y * (g ^ n : M) * y⁻¹, hyR,
    M.mul_mem (M.mul_mem hyM (g ^ n).2) (M.inv_mem hyM), ?_⟩
  have hr : mk ⟨y * (g ^ n : M) * y⁻¹, M.mul_mem (M.mul_mem hyM (g ^ n).2) (M.inv_mem hyM)⟩ =
      yb * l * yb⁻¹ := by
    rw [← hg₃l, hyb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [hr, barM_map_conj hyM]
  refine ⟨⟨l, hlL, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨w, hw, rfl⟩
  have hcw := Subgroup.mem_centralizer_iff.mp hlc w hw
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (yb * l * yb⁻¹)⁻¹ * zb = yb * (l⁻¹ * zb) * yb⁻¹ := by
    calc (yb * l * yb⁻¹)⁻¹ * zb = yb * l⁻¹ * (yb⁻¹ * zb * yb) * yb⁻¹ := by group
      _ = yb * l⁻¹ * zb * yb⁻¹ := by
        rw [show yb⁻¹ * zb * yb = zb by rw [mul_assoc, ← hybz, inv_mul_cancel_left]]
      _ = yb * (l⁻¹ * zb) * yb⁻¹ := by group
  rw [e1]
  calc yb * w * yb⁻¹ * (yb * (l⁻¹ * zb) * yb⁻¹) = yb * (w * (l⁻¹ * zb)) * yb⁻¹ := by group
    _ = yb * ((l⁻¹ * zb) * w) * yb⁻¹ := by rw [hcw]
    _ = yb * (l⁻¹ * zb) * yb⁻¹ * (yb * w * yb⁻¹) := by group



theorem exists_rep_mem_R {z : G} (hzM : z ∈ M)
    (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hin : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' ∧ ∃ r ∈ R, ∃ hrM : r ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩ ∈ barM M L' ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  D1MSideAt.exists_rep_mem_R_at hzM hz3 (fun _ hx => localGroup_le_normalizer_pCoreOf 2 H (hCz hx.2)) hsyl hL hin

end CFSG.AGLEmbedding
