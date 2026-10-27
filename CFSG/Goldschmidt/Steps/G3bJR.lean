module

public import CFSG.Goldschmidt.Steps.G3bL2
public import CFSG.Goldschmidt.Basic
public import CFSG.Walter.Bender1970.S2.OddFitting

public section

namespace CFSG.Goldschmidt.G3b

open CFSG.Open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

theorem normalizer_le_normalizer_centralizer' {G : Type*} [Group G] (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have key : ∀ m ∈ Subgroup.normalizer (S : Set G), ∀ x ∈ Subgroup.centralizer (S : Set G),
      m * x * m⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro m hm x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro s hs
    have hs' : m⁻¹ * s * m⁻¹⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) s).mp hs
    rw [inv_inv] at hs'
    have h := hx _ hs'
    calc s * (m * x * m⁻¹) = m * ((m⁻¹ * s * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * s * m)) * m⁻¹ := by rw [h]
      _ = m * x * m⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have h := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  simpa [mul_assoc] using h

theorem eq_three_of_dvd_six {n : ℕ} (h6 : n ∣ 6) (hodd : ¬ 2 ∣ n) (h1 : n ≠ 1) : n = 3 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases n <;> simp_all

section JR

variable {L : Type} [Group L] [Finite L]

theorem jr_normalizer_facts
    (hJR : IsTypeJR L) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (S : Sylow 2 L) :
    ((Subgroup.centralizer ((S : Subgroup L) : Set L)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup L) : Set L))).index = 21 ∧
    (∃ x ∈ Subgroup.normalizer ((S : Subgroup L) : Set L),
      ∃ x' ∈ Subgroup.normalizer ((S : Subgroup L) : Set L),
        x * x' * x⁻¹ * x'⁻¹ ∉ Subgroup.centralizer ((S : Subgroup L) : Set L)) ∧
    oddCoreOf (Subgroup.centralizer ((S : Subgroup L) : Set L)) =
      (Subgroup.center (Subgroup.normalizer ((S : Subgroup L) : Set L))).map
        (Subgroup.normalizer ((S : Subgroup L) : Set L)).subtype ∧
    IsCyclic (oddCoreOf (Subgroup.centralizer ((S : Subgroup L) : Set L))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup L := hJR.1
  obtain ⟨hSel, hScard⟩ := hJR.sylow_two_of_nonabelian hnonab S
  obtain ⟨g, hgN, hgC, -, hgtrans⟩ :=
    hJR.exists_normalizer_sylow_two_transitive_of_nonabelian hnonab S
  set Sg := (S : Subgroup L) with hSg
  set N := Subgroup.normalizer (Sg : Set L) with hN
  set C := Subgroup.centralizer (Sg : Set L) with hC
  have hSexp : ∀ x ∈ Sg, x ^ 2 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Sg) x hx
  have hcomm : ∀ x ∈ Sg, ∀ y ∈ Sg, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Sg) ⟨y, hy⟩)
  have hSC : Sg ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  have hCN : C ≤ N := fun x hx => mem_normalizer_of_mem_centralizer hx
  have hSN : Sg ≤ N := Subgroup.le_normalizer
  obtain ⟨t, htS, ht1⟩ : ∃ t ∈ Sg, t ≠ 1 := by
    by_contra h
    push Not at h
    have : Sg = ⊥ := (Subgroup.eq_bot_iff_forall Sg).mpr h
    rw [this, Subgroup.card_bot] at hScard
    omega
  have ht2 : orderOf t = 2 := orderOf_eq_prime (hSexp t htS) ht1
  have htt : t * t = 1 := by rw [← pow_two]; exact hSexp t htS
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨-, p, f, hpf, E, hpodd, hf, h5, hEC, hEn, ⟨eE⟩, hCE⟩ := hJR.2.2 t ht2
  have h8 := hJR.mod_eight ht2 E hpodd hf h5 hEC hEn eE hCE
  obtain ⟨hVcard, -, -, -⟩ := hJR.sylow_two_of_mem S htS ht2 E hpodd hf h5 hEC hEn eE hCE
  set V := Sg ⊓ E with hV
  have hVS : V ≤ Sg := inf_le_left
  have hVE : V ≤ E := inf_le_right
  have hCtE : Subgroup.centralizer ({t} : Set L) ≤ Subgroup.normalizer (E : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEC).mp hEn
  have hCCt : C ≤ Subgroup.centralizer ({t} : Set L) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htS)
  have htCE : t ∈ Subgroup.centralizer (E : Set L) :=
    (show t ∈ Subgroup.centralizer ({t} : Set L) ⊓ Subgroup.centralizer (E : Set L) from
      hCE ▸ Subgroup.mem_zpowers t).2
  have hE4 : 4 ≤ Nat.card (GaloisField p f) := by rw [GaloisField.card p f hf.ne']; omega
  have : IsSimpleGroup PSL(2, GaloisField p f) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
  have : IsSimpleGroup E := eE.isSimpleGroup
  have hEnonab : ∃ a b : E, a * b ≠ b * a := exists_mul_ne_mul_of_mulEquiv_psl2 hE4 eE
  have htE : t ∉ E := by
    intro htE
    have hZ : (⟨t, htE⟩ : E) ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp htCE) x x.2)
    rw [center_eq_bot_of_isSimpleGroup hEnonab, Subgroup.mem_bot] at hZ
    exact ht1 (congrArg Subtype.val hZ)
  have hVidx : (V.subgroupOf Sg).index = 2 := by
    have h := (V.subgroupOf Sg).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv, hVcard, hScard] at h
    omega
  have hdecomp : ∀ s ∈ Sg, s ∈ E ∨ s * t ∈ E := by
    intro s hs
    by_cases hsE : s ∈ E
    · exact Or.inl hsE
    · right
      have hs' : (⟨s, hs⟩ : Sg) ∉ V.subgroupOf Sg := fun h' =>
        hsE (Subgroup.mem_subgroupOf.mp h').2
      have ht' : (⟨t, htS⟩ : Sg) ∉ V.subgroupOf Sg := fun h' =>
        htE (Subgroup.mem_subgroupOf.mp h').2
      have h := (Subgroup.mul_mem_iff_of_index_two hVidx (a := ⟨s, hs⟩)
        (b := ⟨t, htS⟩)).mpr (iff_of_false hs' ht')
      exact (Subgroup.mem_subgroupOf.mp h).2
  have hcentS : ∀ n : L, (∀ v ∈ V, n * v * n⁻¹ = v) → n * t * n⁻¹ = t → n ∈ C := by
    intro n hnV hnt
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hns : n * s * n⁻¹ = s := by
      rcases hdecomp s hs with h | h
      · exact hnV s ⟨hs, h⟩
      · have h1 := hnV (s * t) ⟨Sg.mul_mem hs htS, h⟩
        calc n * s * n⁻¹ = (n * (s * t) * n⁻¹) * (n * t * n⁻¹)⁻¹ := by group
          _ = s := by rw [h1, hnt, mul_inv_cancel_right]
    calc s * n = (n * s * n⁻¹) * n := by rw [hns]
      _ = n * s := by group
  have hnormS' : ∀ n : L, n ∈ Subgroup.normalizer (V : Set L) → n * t * n⁻¹ = t →
      ∀ x ∈ Sg, n * x * n⁻¹ ∈ Sg := by
    intro n hnV hnt x hx
    rcases hdecomp x hx with h | h
    · exact hVS ((Subgroup.mem_normalizer_iff.mp hnV x).mp ⟨hx, h⟩)
    · have h1 := hVS ((Subgroup.mem_normalizer_iff.mp hnV (x * t)).mp ⟨Sg.mul_mem hx htS, h⟩)
      have : n * x * n⁻¹ = (n * (x * t) * n⁻¹) * (n * t * n⁻¹)⁻¹ := by group
      rw [this, hnt]
      exact Sg.mul_mem h1 (Sg.inv_mem htS)
  have hnormS : ∀ n : L, n ∈ Subgroup.normalizer (V : Set L) → n * t * n⁻¹ = t → n ∈ N := by
    intro n hnV hnt
    rw [hN, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hnormS' n hnV hnt x, fun hx => ?_⟩
    have hnt' : n⁻¹ * t * n⁻¹⁻¹ = t := by
      rw [inv_inv]
      calc n⁻¹ * t * n = n⁻¹ * (n * t * n⁻¹) * n := by rw [hnt]
        _ = t := by group
    have h := hnormS' n⁻¹ (Subgroup.inv_mem _ hnV) hnt' _ hx
    simpa [mul_assoc] using h
  set φ := Sg.normalizerMonoidHom with hφ
  have hφapp : ∀ (n : N) (x : Sg), ((φ n x : Sg) : L) = (n : L) * x * (n : L)⁻¹ :=
    fun _ _ => rfl
  have hφker : ∀ n : N, φ n = 1 ↔ (n : L) ∈ C := by
    intro n
    rw [← MonoidHom.mem_ker, hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  set Nt := N ⊓ Subgroup.centralizer ({t} : Set L) with hNt
  have hNtN : Nt ≤ N := inf_le_left
  have hCNt : C ≤ Nt := le_inf hCN hCCt
  have hNt7 : (Nt.subgroupOf N).index = 7 := by
    let : MulAction N Sg := MulAction.compHom Sg φ
    have hsmul : ∀ (n : N) (x : Sg), ((n • x : Sg) : L) = (n : L) * x * (n : L)⁻¹ :=
      fun _ _ => rfl
    have hstab : MulAction.stabilizer N (⟨t, htS⟩ : Sg) = Nt.subgroupOf N := by
      ext n
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        refine ⟨n.2, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h' := congrArg Subtype.val h
        rw [hsmul] at h'
        calc (n : L) * t = ((n : L) * t * (n : L)⁻¹) * n := by group
          _ = t * n := by rw [h']
      · intro h
        apply Subtype.ext
        rw [hsmul]
        have h' := Subgroup.mem_centralizer_singleton_iff.mp h.2
        rw [h', mul_inv_cancel_right]
    have horbit : MulAction.orbit N (⟨t, htS⟩ : Sg) = {x : Sg | x ≠ 1} := by
      ext x
      constructor
      · rintro ⟨n, rfl⟩ h
        apply ht1
        have h' := congrArg Subtype.val h
        change (n : L) * t * (n : L)⁻¹ = 1 at h'
        rw [mul_inv_eq_one, mul_eq_left] at h'
        exact h'
      · intro hx
        have hx' : (x : L) ≠ 1 := fun h => hx (Subtype.ext h)
        obtain ⟨k, hk⟩ := hgtrans t htS ht1 x x.2 hx'
        exact ⟨⟨g ^ k, N.pow_mem hgN k⟩, Subtype.ext (by rw [hsmul]; exact hk)⟩
    rw [← hstab, MulAction.index_stabilizer, horbit]
    have : ({x : Sg | x ≠ 1} : Set Sg) = Set.univ \ {1} := by
      ext
      simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hScard]
  have hVEp : IsPGroup 2 (V.subgroupOf E) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv, hVcard]
    norm_num
  obtain ⟨P0, hP0⟩ := hVEp.exists_le_sylow
  have hP0K := sylow_isKleinFour_of_mulEquiv eE hpodd hf h8 P0
  have hP0eq : (P0 : Subgroup E) = V.subgroupOf E := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hP0
    rw [hP0K.card_four, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv, hVcard]
  have hmemP0 : ∀ x : E, x ∈ (P0 : Subgroup E) ↔ (x : L) ∈ Sg := by
    intro x
    rw [hP0eq, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  obtain ⟨hcommE, ⟨Γ, hΓ, hΓmem⟩, ⟨yE, hyEN, vE, hvE, hyv, hyfix⟩⟩ :=
    mulAut_fix_props_of_mulEquiv eE hpodd hf h5 h8 P0
  set ρ := E.normalizerMonoidHom with hρ
  have hρapp : ∀ (n : Subgroup.normalizer (E : Set L)) (x : E),
      ((ρ n x : E) : L) = (n : L) * x * (n : L)⁻¹ := fun _ _ => rfl
  have hρfix : ∀ (n : Subgroup.normalizer (E : Set L)), (n : L) ∈ C →
      ∀ x ∈ (P0 : Subgroup E), ρ n x = x := by
    intro n hn x hx
    apply Subtype.ext
    rw [hρapp]
    have h := Subgroup.mem_centralizer_iff.mp hn x ((hmemP0 x).mp hx)
    rw [← h, mul_inv_cancel_right]
  have hρker : ∀ (n : Subgroup.normalizer (E : Set L)), (n : L) ∈ C → ρ n = 1 →
      (n : L) = 1 ∨ (n : L) = t := by
    intro n hn h1
    have hmem : (n : L) ∈
        Subgroup.centralizer ({t} : Set L) ⊓ Subgroup.centralizer (E : Set L) := by
      refine Subgroup.mem_inf.mpr ⟨hCCt hn, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun a : MulAut E => ((a ⟨x, hx⟩ : E) : L)) h1
      simp only [hρapp, MulAut.one_apply] at h
      calc x * n = ((n : L) * x * (n : L)⁻¹) * n := by rw [h]
        _ = n * x := by group
    rw [hCE] at hmem
    exact eq_one_or_eq_of_mem_zpowers ht2 hmem
  set y := (yE : L) with hy
  have hyE : y ∈ E := yE.2
  have hyCt : y ∈ Subgroup.centralizer ({t} : Set L) := hEC hyE
  have hyt : y * t * y⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hyCt, mul_inv_cancel_right]
  have hyV : y ∈ Subgroup.normalizer (V : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxE : x ∈ E := hVE hx
      have h1 : (⟨x, hxE⟩ : E) ∈ (P0 : Subgroup E) := (hmemP0 _).mpr hx.1
      have h2 := (Subgroup.mem_normalizer_iff.mp hyEN _).mp h1
      rw [hmemP0] at h2
      exact ⟨h2, E.mul_mem (E.mul_mem hyE hxE) (E.inv_mem hyE)⟩
    · intro hx
      have hxE : x ∈ E := by
        have h := E.mul_mem (E.mul_mem (E.inv_mem hyE) hx.2) hyE
        simpa [mul_assoc] using h
      have h1 : yE * ⟨x, hxE⟩ * yE⁻¹ ∈ (P0 : Subgroup E) := (hmemP0 _).mpr hx.1
      have h2 := (Subgroup.mem_normalizer_iff.mp hyEN _).mpr h1
      exact ⟨(hmemP0 _).mp h2, hxE⟩
  have hyN : y ∈ N := hnormS y hyV hyt
  have hyNt : y ∈ Nt := ⟨hyN, hyCt⟩
  have hyC : y ∉ C := by
    intro hyC
    apply hyv
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_iff.mp hyC vE ((hmemP0 vE).mp hvE)
    change y * vE * y⁻¹ = vE
    rw [← h, mul_inv_cancel_right]
  have hCNt3 : (C.subgroupOf Nt).index = 3 := by
    have hNtV : Nt ≤ Subgroup.normalizer (V : Set L) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp hn.1 x
      have h2 := Subgroup.mem_normalizer_iff.mp (hCtE hn.2) x
      exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
    set ψ := V.normalizerMonoidHom.comp (Subgroup.inclusion hNtV) with hψ
    have hψker : ψ.ker = C.subgroupOf Nt := by
      ext n
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        apply hcentS
        · intro v hv
          have h' := congrArg (fun a : MulAut V => ((a ⟨v, hv⟩ : V) : L)) h
          exact h'
        · rw [Subgroup.mem_centralizer_singleton_iff.mp n.2.2, mul_inv_cancel_right]
      · intro h
        ext v
        change (n : L) * v * (n : L)⁻¹ = v
        rw [← Subgroup.mem_centralizer_iff.mp h v (hVS v.2), mul_inv_cancel_right]
    have hVK : IsKleinFour V := by
      have h := isKleinFour_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hVE) (hP0eq ▸ hP0K)
      exact h
    have h6 : (C.subgroupOf Nt).index ∣ 6 := by
      rw [← hψker, Subgroup.index_ker]
      have : IsKleinFour V := hVK
      rw [← kleinFourAut_card V]
      exact Subgroup.card_subgroup_dvd_card _
    have hne1 : (C.subgroupOf Nt).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
      exact fun h => hyC (h hyNt)
    have hodd : ¬ 2 ∣ (C.subgroupOf Nt).index := by
      intro h2
      have h1 : Sg.relIndex N = Sg.relIndex C * C.relIndex N :=
        (Subgroup.relIndex_mul_relIndex _ _ _ hSC hCN).symm
      have h3 : C.relIndex N = C.relIndex Nt * Nt.relIndex N :=
        (Subgroup.relIndex_mul_relIndex _ _ _ hCNt hNtN).symm
      apply S.not_dvd_index
      refine dvd_trans ?_ (Subgroup.relIndex_dvd_index_of_le hSN)
      rw [h1, h3]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
    exact eq_three_of_dvd_six h6 hodd hne1
  have hCN21 : (C.subgroupOf N).index = 21 := by
    have h3 : C.relIndex N = C.relIndex Nt * Nt.relIndex N :=
      (Subgroup.relIndex_mul_relIndex _ _ _ hCNt hNtN).symm
    change C.relIndex N = 21
    rw [h3]
    change (C.subgroupOf Nt).index * (Nt.subgroupOf N).index = 21
    rw [hCNt3, hNt7]
  have hfixall : ∀ m : L, (∀ k : ℕ, (g ^ k)⁻¹ * m * g ^ k ∈
      Subgroup.centralizer ({t} : Set L)) → m ∈ Subgroup.centralizer ({t} : Set L) →
      m ∈ C := by
    intro m hm _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, mul_one]
    obtain ⟨k, hk⟩ := hgtrans t htS ht1 x hx hx1
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hm k)
    rw [← hk]
    calc g ^ k * t * (g ^ k)⁻¹ * m
        = g ^ k * (t * ((g ^ k)⁻¹ * m * g ^ k)) * (g ^ k)⁻¹ := by group
      _ = g ^ k * (((g ^ k)⁻¹ * m * g ^ k) * t) * (g ^ k)⁻¹ := by rw [← h]
      _ = m * (g ^ k * t * (g ^ k)⁻¹) := by group
  refine ⟨hCN21, ?_, ?_⟩
  ·
    refine ⟨g, hgN, y, hyN, fun hw => hyC ?_⟩
    have hwN : g * y * g⁻¹ * y⁻¹ ∈ N := hCN hw
    have hφw : φ ⟨_, hwN⟩ = 1 := (hφker _).mpr hw
    have hcφ : φ ⟨g, hgN⟩ * φ ⟨y, hyN⟩ = φ ⟨y, hyN⟩ * φ ⟨g, hgN⟩ := by
      have h : (⟨g * y * g⁻¹ * y⁻¹, hwN⟩ : N) =
          ⟨g, hgN⟩ * ⟨y, hyN⟩ * ⟨g, hgN⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
      rw [h, map_mul, map_mul, map_mul, map_inv, map_inv] at hφw
      calc φ ⟨g, hgN⟩ * φ ⟨y, hyN⟩
          = (φ ⟨g, hgN⟩ * φ ⟨y, hyN⟩ * (φ ⟨g, hgN⟩)⁻¹ * (φ ⟨y, hyN⟩)⁻¹) *
            (φ ⟨y, hyN⟩ * φ ⟨g, hgN⟩) := by group
        _ = φ ⟨y, hyN⟩ * φ ⟨g, hgN⟩ := by rw [hφw, one_mul]
    have hcomk : ∀ k : ℕ, φ ⟨g, hgN⟩ ^ k * φ ⟨y, hyN⟩ = φ ⟨y, hyN⟩ * φ ⟨g, hgN⟩ ^ k :=
      fun k => (Commute.pow_left hcφ k).eq
    have hyt' : φ ⟨y, hyN⟩ ⟨t, htS⟩ = ⟨t, htS⟩ := Subtype.ext (by rw [hφapp]; exact hyt)
    rw [hC, Subgroup.mem_centralizer_iff]
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, mul_one]
    obtain ⟨k, hk⟩ := hgtrans t htS ht1 x hx hx1
    have hxk : (⟨x, hx⟩ : Sg) = (φ ⟨g, hgN⟩ ^ k) ⟨t, htS⟩ := by
      apply Subtype.ext
      rw [← map_pow, hφapp]
      exact hk.symm
    have hfix : φ ⟨y, hyN⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hxk, ← MulAut.mul_apply, ← hcomk, MulAut.mul_apply, hyt']
    have h := congrArg Subtype.val hfix
    rw [hφapp] at h
    calc x * y = (y * x * y⁻¹) * y := by rw [h]
      _ = y * x := by group
  set Z := oddCoreOf C with hZ
  have hZC : Z ≤ C := Subgroup.map_subtype_le _
  have hZodd : Odd (Nat.card Z) := by
    rw [hZ, oddCoreOf, Subgroup.card_map_of_injective C.subtype_injective,
      goldschmidtOddCore_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hZnormC : ∀ c ∈ C, ∀ z ∈ Z, c * z * c⁻¹ ∈ Z := by
    intro c hc z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have : (goldschmidtOddCore C).Normal := inferInstance
    exact ⟨⟨c, hc⟩ * z' * ⟨c, hc⟩⁻¹, this.conj_mem z' hz' ⟨c, hc⟩, rfl⟩
  have hZN : N ≤ Subgroup.normalizer (Z : Set L) := by
    have : (goldschmidtOddCore C).Characteristic := by
      rw [goldschmidtOddCore_eq_pPrimeCore]
      infer_instance
    exact (normalizer_le_normalizer_centralizer' Sg).trans
      (normalizer_le_normalizer_map_of_characteristic (A := C) (goldschmidtOddCore C))
  have hZt : t ∉ Z := by
    intro htZ
    have h := orderOf_dvd_natCard (⟨t, htZ⟩ : Z)
    rw [Subgroup.orderOf_mk, ht2] at h
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h)
  have hZE : Z ≤ Subgroup.normalizer (E : Set L) := (hZC.trans hCCt).trans hCtE
  have hCE' : C ≤ Subgroup.normalizer (E : Set L) := hCCt.trans hCtE
  have hZcyc : IsCyclic Z := by
    set ρZ := ρ.comp (Subgroup.inclusion hZE) with hρZ
    have hρZodd : ∀ z : Z, Odd (orderOf (ρZ z)) := fun z =>
      Odd.of_dvd_nat (Odd.of_dvd_nat hZodd (orderOf_dvd_natCard z)) (orderOf_map_dvd ρZ z)
    have hρZΓ : ∀ z : Z, ρZ z ∈ Γ := fun z =>
      hΓmem _ (hρZodd z) (hρfix (Subgroup.inclusion hZE z) (hZC z.2))
    have hinj : Function.Injective (ρZ.codRestrict Γ hρZΓ) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro z hz
      have h1 : ρZ z = 1 := congrArg Subtype.val hz
      rcases hρker (Subgroup.inclusion hZE z) (hZC z.2) h1 with h | h
      · exact (Subgroup.mem_bot).mpr (Subtype.ext h)
      · exact absurd (h ▸ z.2) hZt
    have : IsCyclic Γ := hΓ
    exact isCyclic_of_injective _ hinj
  refine ⟨?_, hZcyc⟩
  have hCZ : ∀ c ∈ C, ∀ z ∈ Z, c * z = z * c := by
    intro c hc z hz
    have hcz := hcommE (ρ ⟨c, hCE' hc⟩) (ρ ⟨z, hZE hz⟩) (hρfix ⟨c, hCE' hc⟩ hc)
      (hρfix ⟨z, hZE hz⟩ (hZC hz))
    set w := c * z * c⁻¹ * z⁻¹ with hw
    have hwZ : w ∈ Z := Z.mul_mem (hZnormC c hc z hz) (Z.inv_mem hz)
    have hwNE : w ∈ Subgroup.normalizer (E : Set L) := hZE hwZ
    have hρw : ρ ⟨w, hwNE⟩ = 1 := by
      have h : (⟨w, hwNE⟩ : Subgroup.normalizer (E : Set L)) =
          ⟨c, hCE' hc⟩ * ⟨z, hZE hz⟩ * ⟨c, hCE' hc⟩⁻¹ * ⟨z, hZE hz⟩⁻¹ := rfl
      rw [h, map_mul, map_mul, map_mul, map_inv, map_inv, hcz]
      group
    rcases hρker ⟨w, hwNE⟩ (hZC hwZ) hρw with h | h
    · change w = 1 at h
      calc c * z = w * (z * c) := by rw [hw]; group
        _ = z * c := by rw [h, one_mul]
    · exact absurd (h ▸ hwZ) hZt
  have hyZ : ∀ z ∈ Z, z * y * z⁻¹ = y := by
    intro z hz
    have hoddz : Odd (orderOf z) := by
      have h := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hZodd h
    have hoddρ : Odd (orderOf (ρ ⟨z, hZE hz⟩)) := by
      have h := orderOf_map_dvd ρ ⟨z, hZE hz⟩
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hoddz h
    have h := hyfix (ρ ⟨z, hZE hz⟩) hoddρ (hρfix ⟨z, hZE hz⟩ (hZC hz))
    exact congrArg Subtype.val h
  set CZ := Subgroup.centralizer (Z : Set L) with hCZdef
  have hCCZ : C ≤ CZ := fun c hc => Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (hCZ c hc z hz).symm
  have hyCZ : y ∈ CZ := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    calc z * y = (z * y * z⁻¹) * z := by group
      _ = y * z := by rw [hyZ z hz]
  have hNtCZ : Nt ≤ CZ := by
    have hle : C ⊔ Subgroup.zpowers y ≤ Nt := sup_le hCNt (Subgroup.zpowers_le.mpr hyNt)
    have hCle : C ≤ C ⊔ Subgroup.zpowers y := le_sup_left
    have h1 : C.relIndex Nt = C.relIndex (C ⊔ Subgroup.zpowers y) *
        (C ⊔ Subgroup.zpowers y).relIndex Nt :=
      (Subgroup.relIndex_mul_relIndex _ _ _ hCle hle).symm
    have hne : C.relIndex (C ⊔ Subgroup.zpowers y) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => hyC (h (le_sup_right (a := C) (Subgroup.mem_zpowers y)))
    have h3 : C.relIndex Nt = 3 := hCNt3
    have hdvd : C.relIndex (C ⊔ Subgroup.zpowers y) ∣ 3 := h3 ▸ Dvd.intro _ h1.symm
    have h' : C.relIndex (C ⊔ Subgroup.zpowers y) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne
      · exact h
    rw [h3, h'] at h1
    have h1' : (C ⊔ Subgroup.zpowers y).relIndex Nt = 1 := by omega
    rw [Subgroup.relIndex_eq_one] at h1'
    exact h1'.trans (sup_le hCCZ (Subgroup.zpowers_le.mpr hyCZ))
  have hNCZ : N ≤ CZ := by
    set K := N ⊓ CZ with hK
    have hNtK : Nt ≤ K := le_inf hNtN hNtCZ
    have hKN : K ≤ N := inf_le_left
    have hCK : C ≤ K := hCNt.trans hNtK
    have h1 : C.relIndex N = C.relIndex K * K.relIndex N :=
      (Subgroup.relIndex_mul_relIndex _ _ _ hCK hKN).symm
    have h2 : C.relIndex K = C.relIndex Nt * Nt.relIndex K :=
      (Subgroup.relIndex_mul_relIndex _ _ _ hCNt hNtK).symm
    have h21 : C.relIndex N = 21 := hCN21
    have h3 : C.relIndex Nt = 3 := hCNt3
    rw [h21, h2, h3] at h1
    have hm : Nt.relIndex K ∣ 7 := by
      have : 3 * (Nt.relIndex K * K.relIndex N) = 3 * 7 := by rw [← mul_assoc, ← h1]
      exact Dvd.intro _ (Nat.eq_of_mul_eq_mul_left (by norm_num) this)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hm with h | h
    ·
      exfalso
      rw [Subgroup.relIndex_eq_one] at h
      apply hyC
      refine hfixall y (fun k => ?_) hyCt
      have hgk : g ^ k ∈ N := N.pow_mem hgN k
      have hmem : (g ^ k)⁻¹ * y * g ^ k ∈ K := by
        refine Subgroup.mem_inf.mpr ⟨N.mul_mem (N.mul_mem (N.inv_mem hgk) hyN) hgk, ?_⟩
        rw [hCZdef, Subgroup.mem_centralizer_iff]
        intro z hz
        have hz' : g ^ k * z * (g ^ k)⁻¹ ∈ Z :=
          (Subgroup.mem_normalizer_iff.mp (hZN hgk) z).mp hz
        have hc := Subgroup.mem_centralizer_iff.mp hyCZ _ hz'
        calc z * ((g ^ k)⁻¹ * y * g ^ k)
            = (g ^ k)⁻¹ * ((g ^ k * z * (g ^ k)⁻¹) * y) * g ^ k := by group
          _ = (g ^ k)⁻¹ * (y * (g ^ k * z * (g ^ k)⁻¹)) * g ^ k := by rw [hc]
          _ = (g ^ k)⁻¹ * y * g ^ k * z := by group
      exact (h hmem).2
    · rw [h] at h1
      have h1' : K.relIndex N = 1 := by omega
      rw [Subgroup.relIndex_eq_one] at h1'
      exact h1'.trans inf_le_right
  apply le_antisymm
  ·
    intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hCN (hZC hz)⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hNCZ n.2) z hz).symm
  ·
    set W := (Subgroup.center N).map N.subtype with hW
    have hWC : W ≤ C := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨s, hSN hs⟩)
    have hWcent : ∀ w ∈ W, ∀ n ∈ N, n * w = w * n := by
      rintro _ ⟨w, hw, rfl⟩ n hn
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨n, hn⟩)
    have hWodd : Odd (Nat.card W) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2
      have hw2 : orderOf (w : L) = 2 := by rw [Subgroup.orderOf_coe, hw]
      have hwC : (w : L) ∈ C := hWC w.2
      have hwS : (w : L) ∈ Sg := by
        have hwp : IsPGroup 2 (Subgroup.zpowers (w : L)) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw2, pow_one])
        have hwN' : Subgroup.zpowers (w : L) ≤ Subgroup.normalizer (Sg : Set L) := by
          rw [Subgroup.zpowers_le]
          exact mem_normalizer_of_mem_centralizer hwC
        have hQp : IsPGroup 2 (Sg ⊔ Subgroup.zpowers (w : L) : Subgroup L) := by
          rw [sup_comm]
          exact hwp.to_sup_of_normal_right' S.isPGroup' hwN'
        have heq : Sg ⊔ Subgroup.zpowers (w : L) = Sg := S.is_maximal' hQp le_sup_left
        exact heq ▸ (le_sup_right (a := Sg) (Subgroup.mem_zpowers (w : L)))
      have hw1 : (w : L) ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hw2
        omega
      obtain ⟨x, hxS, hx1, hxw⟩ : ∃ x ∈ Sg, x ≠ 1 ∧ x ≠ (w : L) := by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ha1, hb1, hab⟩ :=
          exists_ne_one_ne_of_three_le_card' (H := Sg) (by rw [hScard]; norm_num)
        by_cases haw : a = (w : L)
        · exact ⟨b, hb, fun h => hb1 (Subtype.ext h),
            fun h => hab (Subtype.ext (show a = b by rw [haw, h]))⟩
        · exact ⟨a, ha, fun h => ha1 (Subtype.ext h), haw⟩
      obtain ⟨k, hk⟩ := hgtrans (w : L) hwS hw1 x hxS hx1
      apply hxw
      rw [← hk, hWcent (w : L) w.2 (g ^ k) (N.pow_mem hgN k), mul_inv_cancel_right]
    intro x hx
    have hxC : x ∈ C := hWC hx
    have hWnorm : (W.subgroupOf C).Normal := by
      constructor
      intro a ha c
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have h := hWcent (a : L) ha (c : L) (hCN c.2)
      change (c : L) * a * (c : L)⁻¹ ∈ W
      rw [h, mul_inv_cancel_right]
      exact ha
    have hWsub : W.subgroupOf C ≤ goldschmidtOddCore C := by
      rw [goldschmidtOddCore_eq_pPrimeCore]
      apply le_sSup
      refine ⟨hWnorm, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
      exact Nat.coprime_two_left.mpr hWodd
    exact ⟨⟨x, hxC⟩, hWsub (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end JR

end CFSG.Goldschmidt.G3b
