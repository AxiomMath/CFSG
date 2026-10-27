module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma49d

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem sq_mem_of_relIndex_two {G : Type*} [Group G] {U K : Subgroup G}
    (hUK : U.relIndex K = 2) {a : G} (ha : a ∈ K) : a ^ 2 ∈ U := by
  by_cases haU : a ∈ U
  · exact pow_mem haU 2
  · have := inv_mul_mem_of_relIndex_two hUK (inv_mem ha) ha (fun h' => haU (inv_mem_iff.mp h'))
      haU
    rwa [inv_inv, ← sq] at this

theorem conj_mem_of_relIndex_two {G : Type*} [Group G] {U K : Subgroup G}
    (hUK : U.relIndex K = 2) (hle : U ≤ K) {k x : G} (hk : k ∈ K) (hx : x ∈ U) :
    k * x * k⁻¹ ∈ U := by
  have hn : (U.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hUK
  exact Subgroup.mem_subgroupOf.1
    (hn.conj_mem ⟨x, hle hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨k, hk⟩)

theorem sq_not_mem_of_not_mem {G : Type*} [Group G] {T S V : Subgroup G} (hSV : S ≤ V)
    (hTn : ∀ v ∈ V, ∀ x ∈ T, v * x * v⁻¹ ∈ T) (hST : T.relIndex S = 2)
    (hSV2 : S.relIndex V = 2) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀T : v₀ ^ 2 ∉ T) {v : G} (hv : v ∈ V)
    (hvS : v ∉ S) : v ^ 2 ∉ T := by
  intro hv2
  have hv₀S : v₀ ∉ S := fun h' => hv₀T (sq_mem_of_relIndex_two hST h')
  have hs := inv_mul_mem_of_relIndex_two hSV2 hv hv₀ hvS hv₀S
  apply hv₀T
  have hv₀e : v₀ = v * (v⁻¹ * v₀) := by group
  rw [hv₀e]
  by_cases hsT : v⁻¹ * v₀ ∈ T
  · have h1 := hTn v hv _ hsT
    have : (v * (v⁻¹ * v₀)) ^ 2 = (v * (v⁻¹ * v₀) * v⁻¹) * v ^ 2 * (v⁻¹ * v₀) := by
      rw [sq (v * (v⁻¹ * v₀)), sq v]
      group
    rw [this]
    exact mul_mem (mul_mem h1 hv2) hsT
  · have hvs : v * (v⁻¹ * v₀) * v⁻¹ ∈ S := conj_mem_of_relIndex_two hSV2 hSV hv hs
    have hvsT : v * (v⁻¹ * v₀) * v⁻¹ ∉ T := by
      intro h'
      apply hsT
      have h2 := hTn v⁻¹ (inv_mem hv) _ h'
      have : v⁻¹ * (v * (v⁻¹ * v₀) * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * v₀ := by group
      rwa [this] at h2
    have hτ := inv_mul_mem_of_relIndex_two hST hs hvs hsT hvsT
    have hs2 := sq_mem_of_relIndex_two hST hs
    have h3 := hTn _ (hSV hs) _ (mul_mem hτ hv2)
    have : (v * (v⁻¹ * v₀)) ^ 2 = (v⁻¹ * v₀) *
        ((v⁻¹ * v₀)⁻¹ * (v * (v⁻¹ * v₀) * v⁻¹) * v ^ 2) * (v⁻¹ * v₀)⁻¹ * (v⁻¹ * v₀) ^ 2 := by
      rw [sq (v * (v⁻¹ * v₀)), sq v, sq (v⁻¹ * v₀)]
      group
    rw [this]
    exact mul_mem h3 hs2

theorem dihedral_parity_of_conj {m : ℕ} (hm : 1 ≤ m) {i j : ZMod (2 ^ m)}
    {c : DihedralGroup (2 ^ m)} (h : c⁻¹ * DihedralGroup.sr i * c = DihedralGroup.sr j) :
    ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) i =
      ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) j := by
  rcases c with k | k
  · rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h
    rw [← DihedralGroup.sr.inj h, map_add, map_sub, map_neg]
    generalize ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) i = a
    generalize ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) k = b
    revert a b
    decide
  · rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr] at h
    rw [← DihedralGroup.sr.inj h, map_sub, map_sub]
    generalize ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) i = a
    generalize ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) k = b
    revert a b
    decide

theorem dihedral_exists_conj_of_parity {m : ℕ} (hm : 1 ≤ m) {i j : ZMod (2 ^ m)}
    (h : ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) i =
      ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) j) :
    ∃ c : DihedralGroup (2 ^ m), c⁻¹ * DihedralGroup.sr i * c = DihedralGroup.sr j := by
  have hval : ∀ a : ZMod (2 ^ m),
      ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) a = (a.val : ZMod 2) := by
    intro a
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have h0 : (((j - i).val : ℕ) : ZMod 2) = 0 := by
    rw [← hval, map_sub]
    exact sub_eq_zero.mpr h.symm
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ 2).mp h0
  refine ⟨DihedralGroup.r (q : ZMod (2 ^ m)), ?_⟩
  rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  congr 1
  have hd : j - i = ((2 * q : ℕ) : ZMod (2 ^ m)) := by rw [← hq, ZMod.natCast_zmod_val]
  push_cast at hd
  linear_combination (-1 : ZMod (2 ^ m)) * hd

theorem exists_eq_sr {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
    (e : ↥D ≃* DihedralGroup (2 ^ m)) {z : G} (hz : D ⊓ centralizer (D : Set G) = zpowers z)
    {y : ↥D} (hy2 : (y : G) ^ 2 = 1) (hyz : (y : G) ∉ zpowers z) :
    ∃ i, e y = DihedralGroup.sr i := by
  rcases hey : e y with i | i
  · exfalso
    apply hyz
    have h2 : (e y) ^ 2 = 1 := by
      rw [← map_pow, show y ^ 2 = 1 from Subtype.ext (by simpa using hy2), map_one]
    rw [hey, sq, DihedralGroup.r_mul_r] at h2
    have hi : 2 * i = 0 := by
      rw [two_mul]
      exact DihedralGroup.r.inj (h2.trans DihedralGroup.one_def)
    have hc := r_mem_center_of_two_mul i hi
    rw [← hz]
    refine Subgroup.mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hcomm := (Subgroup.mem_center_iff.mp hc) (e ⟨d, hd⟩)
    rw [← hey, ← map_mul, ← map_mul] at hcomm
    have := congrArg Subtype.val (e.injective hcomm)
    simpa using this
  · exact ⟨i, rfl⟩

theorem exists_conj_sq_eq {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
    (e : ↥D ≃* DihedralGroup (2 ^ m)) (hm : 3 ≤ m) {z : G}
    (hz : D ⊓ centralizer (D : Set G) = zpowers z) {g : G}
    (hgD : ∀ d ∈ D, g⁻¹ * d * g ∈ D) (hgD' : ∀ d ∈ D, g * d * g⁻¹ ∈ D) {y : G} (hyD : y ∈ D)
    (hy2 : y ^ 2 = 1) (hyz : y ∉ zpowers z) :
    ∃ c ∈ D, (g ^ 2)⁻¹ * y * g ^ 2 = c⁻¹ * y * c := by
  set par := ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) with hpar
  have hnc : ∀ a ∈ D, a ∉ zpowers z → g⁻¹ * a * g ∉ zpowers z := by
    intro a ha haz hga
    apply haz
    rw [← hz] at hga ⊢
    refine Subgroup.mem_inf.mpr ⟨ha, mem_centralizer_iff.mpr fun d hd => ?_⟩
    have h1 := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hga).2 _ (hgD d hd)
    calc d * a = g * ((g⁻¹ * d * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * (g⁻¹ * d * g)) * g⁻¹ := by rw [h1]
      _ = a * d := by group
  have hsq : ∀ a : G, a ^ 2 = 1 → (g⁻¹ * a * g) ^ 2 = 1 := by
    intro a ha
    have : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by
      rw [sq, sq]
      group
    rw [this, ha, mul_one, inv_mul_cancel]
  have hto : ∀ (a b : G) (ha : a ∈ D) (hb : b ∈ D) (i j : ZMod (2 ^ m)),
      e ⟨a, ha⟩ = DihedralGroup.sr i → e ⟨b, hb⟩ = DihedralGroup.sr j →
      (∃ c ∈ D, c⁻¹ * a * c = b) → par i = par j := by
    rintro a b ha hb i j hai hbj ⟨c, hc, hcab⟩
    refine dihedral_parity_of_conj (by omega) (c := e ⟨c, hc⟩) ?_
    rw [← hai, ← hbj, ← map_inv e, ← map_mul e, ← map_mul e]
    congr 1
    exact Subtype.ext hcab
  have hfrom : ∀ (a b : G) (ha : a ∈ D) (hb : b ∈ D) (i j : ZMod (2 ^ m)),
      e ⟨a, ha⟩ = DihedralGroup.sr i → e ⟨b, hb⟩ = DihedralGroup.sr j →
      par i = par j → ∃ c ∈ D, c⁻¹ * a * c = b := by
    intro a b ha hb i j hai hbj hij
    obtain ⟨c', hc'⟩ := dihedral_exists_conj_of_parity (by omega) hij
    refine ⟨(e.symm c' : G), (e.symm c').2, ?_⟩
    have : (e.symm c')⁻¹ * ⟨a, ha⟩ * e.symm c' = ⟨b, hb⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hai, hbj, hc']
    exact congrArg Subtype.val this
  have hy₁D := hgD y hyD
  have hy₂D := hgD _ hy₁D
  obtain ⟨i₀, hi₀⟩ := exists_eq_sr e hz (y := ⟨y, hyD⟩) hy2 hyz
  obtain ⟨i₁, hi₁⟩ := exists_eq_sr e hz (y := ⟨_, hy₁D⟩) (hsq y hy2) (hnc y hyD hyz)
  obtain ⟨i₂, hi₂⟩ := exists_eq_sr e hz (y := ⟨_, hy₂D⟩) (hsq _ (hsq y hy2))
    (hnc _ hy₁D (hnc y hyD hyz))
  have hgoal : (g ^ 2)⁻¹ * y * g ^ 2 = g⁻¹ * (g⁻¹ * y * g) * g := by
    rw [sq]
    group
  rw [hgoal]
  by_cases h01 : par i₀ = par i₁
  · obtain ⟨c₁, hc₁, hc₁e⟩ := hfrom _ _ hyD hy₁D i₀ i₁ hi₀ hi₁ h01
    refine ⟨c₁ * (g⁻¹ * c₁ * g), mul_mem hc₁ (hgD c₁ hc₁), ?_⟩
    calc g⁻¹ * (g⁻¹ * y * g) * g = g⁻¹ * (c₁⁻¹ * y * c₁) * g := by rw [hc₁e]
      _ = g⁻¹ * c₁⁻¹ * g * (g⁻¹ * y * g) * (g⁻¹ * c₁ * g) := by group
      _ = g⁻¹ * c₁⁻¹ * g * (c₁⁻¹ * y * c₁) * (g⁻¹ * c₁ * g) := by rw [hc₁e]
      _ = (c₁ * (g⁻¹ * c₁ * g))⁻¹ * y * (c₁ * (g⁻¹ * c₁ * g)) := by group
  · have h12 : par i₁ ≠ par i₂ := by
      intro h12
      obtain ⟨c₂, hc₂, hc₂e⟩ := hfrom _ _ hy₁D hy₂D i₁ i₂ hi₁ hi₂ h12
      apply h01
      refine hto _ _ hyD hy₁D i₀ i₁ hi₀ hi₁ ⟨g * c₂ * g⁻¹, hgD' c₂ hc₂, ?_⟩
      calc (g * c₂ * g⁻¹)⁻¹ * y * (g * c₂ * g⁻¹) = g * (c₂⁻¹ * (g⁻¹ * y * g) * c₂) * g⁻¹ := by
            group
        _ = g * (g⁻¹ * (g⁻¹ * y * g) * g) * g⁻¹ := by rw [hc₂e]
        _ = g⁻¹ * y * g := by group
    have h02 : par i₀ = par i₂ := by
      revert h01 h12
      generalize par i₀ = a
      generalize par i₁ = b
      generalize par i₂ = c
      revert a b c
      decide
    obtain ⟨c, hc, hce⟩ := hfrom _ _ hyD hy₂D i₀ i₂ hi₀ hi₂ h02
    exact ⟨c, hc, hce.symm⟩

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem u_not_mem_tD [Finite X] (hσ : Setup42 h hS w z) :
    w ^ (orderOf w / 2) ∉ zpowers t ⊔ (S ⊓ L) := by
  intro hu
  have hu' : w ^ (orderOf w / 2) ∈ (zpowers t ⊔ (S ⊓ L)) ⊓ zpowers w :=
    Subgroup.mem_inf.mpr ⟨hu, pow_mem (mem_zpowers w) _⟩
  rw [hσ.disj, Subgroup.mem_bot] at hu'
  have := hσ.orderOf_u
  rw [hu', orderOf_one] at this
  exact absurd this (by norm_num)

theorem mem_X_tD [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hxX : x ∈ closure {t, w ^ (orderOf w / 2), z}) (hxD : x ∈ zpowers t ⊔ (S ⊓ L)) :
    ∃ a c : X, (a = 1 ∨ a = t) ∧ (c = 1 ∨ c = z) ∧ x = a * c := by
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := hσ.mem_X hxX
  rcases hb with hb | hb
  · exact ⟨a, c, ha, hc, by rw [hb, mul_one]⟩
  · exfalso
    apply hσ.u_not_mem_tD
    have haD : a ∈ zpowers t ⊔ (S ⊓ L) := by
      rcases ha with ha | ha <;> rw [ha]
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers t)
    have hcD : c ∈ zpowers t ⊔ (S ⊓ L) := by
      rcases hc with hc | hc <;> rw [hc]
      · exact one_mem _
      · exact mem_sup_right hσ.z_mem
    have : w ^ (orderOf w / 2) = a⁻¹ * (a * b * c) * c⁻¹ := by rw [hb]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem haD) hxD) (inv_mem hcD)

theorem mem_X_not_tD [Finite X] (hσ : Setup42 h hS w z) {x : X}
    (hxX : x ∈ closure {t, w ^ (orderOf w / 2), z}) (hxD : x ∉ zpowers t ⊔ (S ⊓ L)) :
    ∃ i j : ℕ, x = w ^ (orderOf w / 2) * t ^ i * z ^ j := by
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := hσ.mem_X hxX
  have hut : w ^ (orderOf w / 2) * t = t * w ^ (orderOf w / 2) :=
    mem_centralizer_singleton_iff.mp (hS.le hσ.u_mem)
  rcases hb with hb | hb
  · exfalso
    apply hxD
    rw [hb, mul_one]
    refine mul_mem ?_ ?_
    · rcases ha with ha | ha <;> rw [ha]
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers t)
    · rcases hc with hc | hc <;> rw [hc]
      · exact one_mem _
      · exact mem_sup_right hσ.z_mem
  · rcases ha with ha | ha <;> rcases hc with hc | hc
    · exact ⟨0, 0, by rw [ha, hb, hc]; simp⟩
    · exact ⟨0, 1, by rw [ha, hb, hc]; simp⟩
    · refine ⟨1, 0, ?_⟩
      rw [ha, hb, hc]
      simp only [pow_one, pow_zero, mul_one]
      exact hut.symm
    · refine ⟨1, 1, ?_⟩
      rw [ha, hb, hc]
      simp only [pow_one]
      rw [hut]

theorem conj_t_eq [Finite X] (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : V ≤ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
    (hST : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hSn : ∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S)
    {v : X} (hv : v ∈ V) : v * t * v⁻¹ = t ∨ v * t * v⁻¹ = t * z := by
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have htS : t ∈ S := h.t_mem hS
  have hyX : v * t * v⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
    (mem_normalizer_iff.mp (hσ.normalizer_T_le_normalizer_X (hV hv)) t).mp htX
  have hyZ : v * t * v⁻¹ ∈ S ⊓ centralizer (S : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨hSn v hv t htS, mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : v⁻¹ * s * v⁻¹⁻¹ ∈ S := hSn v⁻¹ (inv_mem hv) s hs
    rw [inv_inv] at hs'
    have hc := mem_centralizer_singleton_iff.mp (hS.le hs')
    calc s * (v * t * v⁻¹) = v * ((v⁻¹ * s * v) * t) * v⁻¹ := by group
      _ = v * (t * (v⁻¹ * s * v)) * v⁻¹ := by rw [hc]
      _ = v * t * v⁻¹ * s := by group
  have hZ := (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.2.2.2.1 hST
  rw [hZ, hσ.center_D] at hyZ
  have hyD : v * t * v⁻¹ ∈ zpowers t ⊔ (S ⊓ L) :=
    (sup_le_sup_left (zpowers_le.mpr hσ.z_mem) _) hyZ
  obtain ⟨a, c, ha, hc, hac⟩ := hσ.mem_X_tD hyX hyD
  have h1 : v * t * v⁻¹ ≠ 1 := by
    intro h1
    have ht1 : t = 1 := by
      calc t = v⁻¹ * (v * t * v⁻¹) * v := by group
        _ = 1 := by rw [h1]; group
    have ht := h.config.orderOf_eq
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hz := hσ.conj_t_ne_z v
  rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
  · exact (h1 (by rw [hac, mul_one])).elim
  · exact (hz (by rw [hac, one_mul])).elim
  · left
    rw [hac, mul_one]
  · right
    exact hac

theorem exists_conj_t_eq_tz [Finite X] (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
    (hSn : ∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S) : ∃ v ∈ V, v * t * v⁻¹ = t * z := by
  have hne := hσ.ne_of_isSylowOf_normalizer hV hSV
  obtain ⟨v, hv, hvS⟩ : ∃ v ∈ V, v ∉ S := by
    by_contra hall
    push Not at hall
    exact hne (le_antisymm hSV fun x hx => hall x hx)
  refine ⟨v, hv, (hσ.conj_t_eq hV.le hST hSn hv).resolve_left fun h1 => hvS ?_⟩
  rw [← hσ.inf_centralizer_t hV hSV]
  refine Subgroup.mem_inf.mpr ⟨hv, mem_centralizer_singleton_iff.mpr ?_⟩
  calc v * t = (v * t * v⁻¹) * v := by group
    _ = t * v := by rw [h1]

theorem mem_T_of_comm [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2)
    (hSV2 : S.relIndex V = 2) {v₀ : X} (hv₀ : v₀ ∈ V)
    (hv₀T : v₀ ^ 2 ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) {x : X}
    (hxX : x ∈ closure {t, w ^ (orderOf w / 2), z}) (hxD : x ∉ zpowers t ⊔ (S ⊓ L)) {v : X}
    (hv : v ∈ V) (hvx : v * x = x * v) : v ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  obtain ⟨i, j, hx⟩ := hσ.mem_X_not_tD hxX hxD
  have hSyl := hσ.isSylowOf_centralizer hKC i j
  rw [← hx] at hSyl
  have hTV : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ V := hσ.T_le.trans hSV
  have hP : V ⊓ (centralizer ({t} : Set X) ⊓ centralizer ({x} : Set X)) =
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
    hSyl.eq_of_le (le_inf hTV hSyl.le) inf_le_right (hV.isPGroup.to_le inf_le_left)
  have hmem : ∀ y ∈ V, y ∈ centralizer ({t} : Set X) → y * x = x * y →
      y ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    intro y hy hyt hyx
    rw [← hP]
    exact Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_inf.mpr ⟨hyt,
      mem_centralizer_singleton_iff.mpr hyx⟩⟩
  by_cases hvt : v ∈ centralizer ({t} : Set X)
  · exact hmem v hv hvt hvx
  · exfalso
    have hvS : v ∉ S := fun h' => hvt (hS.le h')
    have hTn : ∀ y ∈ V, ∀ x' ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w,
        y * x' * y⁻¹ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
      fun y hy x' hx' => (mem_normalizer_iff.mp (hV.le hy) x').mp hx'
    apply sq_not_mem_of_not_mem hSV hTn hST hSV2 hv₀ hv₀T hv hvS
    refine hmem _ (pow_mem hv 2) (hS.le (sq_mem_of_relIndex_two hSV2 hv)) ?_
    calc v ^ 2 * x = v * (v * x) := by rw [sq, mul_assoc]
      _ = v * (x * v) := by rw [hvx]
      _ = (v * x) * v := by rw [mul_assoc]
      _ = (x * v) * v := by rw [hvx]
      _ = x * v ^ 2 := by rw [sq, mul_assoc]

theorem conj_not_mem_of_mem_normalizer [Finite X] (hKF : AutPSL2FusionInput)
    (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
    (hSn : ∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S) {n : X}
    (hn : n ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) {x : X}
    (hxX : x ∈ closure {t, w ^ (orderOf w / 2), z}) (hxD : x ∉ zpowers t ⊔ (S ⊓ L)) :
    n * x * n⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} ∧
      n * x * n⁻¹ ∉ zpowers t ⊔ (S ⊓ L) := by
  have hyX : n * x * n⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
    (mem_normalizer_iff.mp (hσ.normalizer_T_le_normalizer_X hn) x).mp hxX
  refine ⟨hyX, fun hyD => hxD ?_⟩
  obtain ⟨a, c, ha, hc, hac⟩ := hσ.mem_X_tD hyX hyD
  have hn' : n⁻¹ ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    inv_mem hn
  obtain ⟨v, hv, hvt⟩ := hσ.exists_conj_V hKF hV hSV hn'
  have hnt : n⁻¹ * t * n ∈ zpowers t ⊔ (S ⊓ L) := by
    have : n⁻¹ * t * n = v * t * v⁻¹ := by rw [hvt, inv_inv]
    rw [this]
    rcases hσ.conj_t_eq hV.le hST hSn hv with h1 | h1 <;> rw [h1]
    · exact mem_sup_left (mem_zpowers t)
    · exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hσ.z_mem)
  have hnz : n⁻¹ * z * n = z := by
    have := hσ.conj_z_of_mem_normalizer_T hn'
    rwa [inv_inv] at this
  have hx : x = (n⁻¹ * a * n) * (n⁻¹ * c * n) := by
    calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
      _ = n⁻¹ * (a * c) * n := by rw [hac]
      _ = (n⁻¹ * a * n) * (n⁻¹ * c * n) := by group
  rw [hx]
  refine mul_mem ?_ ?_
  · rcases ha with ha | ha <;> rw [ha]
    · rw [mul_one, inv_mul_cancel]
      exact one_mem _
    · exact hnt
  · rcases hc with hc | hc <;> rw [hc]
    · rw [mul_one, inv_mul_cancel]
      exact one_mem _
    · rw [hnz]
      exact mem_sup_right hσ.z_mem

theorem eq_T_of_le_centralizer [Finite X] (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2)
    (hSV2 : S.relIndex V = 2) {v₀ : X} (hv₀ : v₀ ∈ V)
    (hv₀T : v₀ ^ 2 ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) {x : X}
    (hxX : x ∈ closure {t, w ^ (orderOf w / 2), z}) (hxD : x ∉ zpowers t ⊔ (S ⊓ L))
    {W : Subgroup X} (hW : IsPGroup 2 W) (hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W)
    (hWx : W ≤ centralizer ({x} : Set X)) : W = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  have hST' : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    intro heq
    rw [← heq, Subgroup.relIndex_self] at hST
    exact absurd hST (by norm_num)
  have hSn : ∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S := fun v hv s hs =>
    conj_mem_of_relIndex_two hSV2 hSV hv hs
  by_contra hne
  have : Group.IsNilpotent ↥W := hW.isNilpotent
  have hlt : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).subgroupOf W < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm (fun y hy => ?_) hTW)
    have : (⟨y, hy⟩ : ↥W) ∈ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).subgroupOf W := htop ▸ mem_top _
    exact this
  obtain ⟨y, hyN, hyT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyNT : (y : X) ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact (mem_normalizer_iff.mp hyN ⟨g, hTW hg⟩).mp hg
    · intro hg
      have hgW : g ∈ W := by
        have h1 : (y : X) * g * (y : X)⁻¹ ∈ W := hTW hg
        have h2 := W.mul_mem (W.mul_mem (W.inv_mem y.2) h1) y.2
        simpa [mul_assoc] using h2
      exact (mem_normalizer_iff.mp hyN ⟨g, hgW⟩).mpr hg
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge (hW.to_le (inf_le_left :
    W ⊓ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) ≤ W))
    inf_le_right
  obtain ⟨k, hk, hkQ⟩ := hV.exists_mem_conj hQ
  have hyQ : (y : X) ∈ Q := hPQ (Subgroup.mem_inf.mpr ⟨y.2, hyNT⟩)
  have hkyV : k⁻¹ * y * k ∈ V := (hkQ y).mp hyQ
  have hkyT : k⁻¹ * y * k ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    intro h1
    apply hyT
    have h2 := (mem_normalizer_iff.mp hk _).mp h1
    have : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
    rw [this] at h2
    exact h2
  have hk' : k⁻¹ ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    inv_mem hk
  obtain ⟨hx'X, hx'D⟩ := hσ.conj_not_mem_of_mem_normalizer hKF hV hSV hST' hSn hk' hxX hxD
  rw [inv_inv] at hx'X hx'D
  apply hkyT
  refine hσ.mem_T_of_comm hKC hV hSV hST hSV2 hv₀ hv₀T hx'X hx'D hkyV ?_
  have hyx := mem_centralizer_singleton_iff.mp (hWx y.2)
  calc k⁻¹ * y * k * (k⁻¹ * x * k) = k⁻¹ * (y * x) * k := by group
    _ = k⁻¹ * (x * y) * k := by rw [hyx]
    _ = k⁻¹ * x * k * (k⁻¹ * y * k) := by group

theorem conj_ne_z_of_not_mem [Finite X] (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2)
    (hSV2 : S.relIndex V = 2) {v₀ : X} (hv₀ : v₀ ∈ V)
    (hv₀T : v₀ ^ 2 ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) {x : X}
    (hxX : x ∈ closure {t, w ^ (orderOf w / 2), z}) (hxD : x ∉ zpowers t ⊔ (S ⊓ L)) (g : X) :
    g * x * g⁻¹ ≠ z := by
  intro hg
  have hTx : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({x} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hσ.X_le_center_T hxX).2 y hy)
  obtain ⟨W, hWs, hTW⟩ := exists_isSylowOf_ge (hS.isPGroup.to_le hσ.T_le) hTx
  have hWT := hσ.eq_T_of_le_centralizer hKF hKC hV hSV hST hSV2 hv₀ hv₀T hxX hxD hWs.isPGroup
    hTW hWs.le
  have hV'x : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({x} : Set X) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hvz := hσ.conj_z_of_mem_normalizer_T (hV.le hv)
    have hx : x = g⁻¹ * z * g := by rw [← hg]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hx]
    calc g⁻¹ * v * g * (g⁻¹ * z * g) = g⁻¹ * (v * z * v⁻¹) * v * g := by group
      _ = g⁻¹ * z * v * g := by rw [hvz]
      _ = g⁻¹ * z * g * (g⁻¹ * v * g) := by group
  have hV'2 : IsPGroup 2 (V.map (MulAut.conj g⁻¹).toMonoidHom) := hV.isPGroup.map _
  obtain ⟨W', hW's, hV'W'⟩ := exists_isSylowOf_ge hV'2 hV'x
  have hc1 : Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hc2 : Nat.card W' = Nat.card W := by rw [hW's.card_eq, hWs.card_eq]
  have hc3 := Subgroup.card_le_of_le hV'W'
  have h1 := Subgroup.relIndex_mul_card (H := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (K := S)
  have h2 := Subgroup.relIndex_mul_card (H := S) (K := V)
  rw [inf_of_le_left hσ.T_le, hST] at h1
  rw [inf_of_le_left hSV, hSV2] at h2
  have hpos : 0 < Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := Nat.card_pos
  rw [hc1, hc2, hWT] at hc3
  omega

theorem mem_D_of_conj_eq_z [Finite X] (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2)
    (hSV2 : S.relIndex V = 2) {v₀ : X} (hv₀ : v₀ ∈ V)
    (hv₀T : v₀ ^ 2 ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) {τ : X}
    (hτT : τ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hτ2 : τ ^ 2 = 1) {g : X}
    (hg : g * τ * g⁻¹ = z) : τ ∈ S ⊓ L := by
  have hST' : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    intro heq
    rw [← heq, Subgroup.relIndex_self] at hST
    exact absurd hST (by norm_num)
  have hSn : ∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S := fun v hv s hs =>
    conj_mem_of_relIndex_two hSV2 hSV hv hs
  obtain ⟨k, hkH, hkX⟩ := hσ.exists_conj_mem_X hKF hτT hτ2
  have hxz : (g * k⁻¹) * (k * τ * k⁻¹) * (g * k⁻¹)⁻¹ = z := by rw [← hg]; group
  by_cases hxD : k * τ * k⁻¹ ∈ zpowers t ⊔ (S ⊓ L)
  · obtain ⟨a, c, ha, hc, hac⟩ := hσ.mem_X_tD hkX hxD
    rcases ha with ha | ha
    · rw [ha, one_mul] at hac
      rcases hc with hc | hc
      · exfalso
        rw [hc] at hac
        rw [hac] at hxz
        have hz1 : z = 1 := by rw [← hxz]; group
        have := hσ.z_order
        rw [hz1, orderOf_one] at this
        exact absurd this (by norm_num)
      · rw [hc] at hac
        have hτ : τ = k⁻¹ * z * k := by
          calc τ = k⁻¹ * (k * τ * k⁻¹) * k := by group
            _ = k⁻¹ * z * k := by rw [hac]
        refine Subgroup.mem_inf.mpr ⟨hσ.T_le hτT, ?_⟩
        rw [hτ]
        have := (mem_normalizer_iff.mp (h.centralizer_le_normalizer (inv_mem hkH)) z).mp
          hσ.z_mem.2
        simpa using this
    · exfalso
      rw [ha] at hac
      rcases hc with hc | hc <;> rw [hc] at hac
      · rw [mul_one] at hac
        rw [hac] at hxz
        exact hσ.conj_t_ne_z _ hxz
      · obtain ⟨v, -, hvt⟩ := hσ.exists_conj_t_eq_tz hV hSV hST' hSn
        rw [hac, ← hvt] at hxz
        exact hσ.conj_t_ne_z (g * k⁻¹ * v) (by rw [← hxz]; group)
  · exact absurd hxz (hσ.conj_ne_z_of_not_mem hKF hKC hV hSV hST hSV2 hv₀ hv₀T hkX hxD _)

theorem conj_mem_D_of_mem_V [Finite X] (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2)
    (hSV2 : S.relIndex V = 2) {v₀ : X} (hv₀ : v₀ ∈ V)
    (hv₀T : v₀ ^ 2 ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) {v d : X} (hv : v ∈ V)
    (hd : d ∈ S ⊓ L) : v * d * v⁻¹ ∈ S ⊓ L := by
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_left.trans' le_sup_right
  have key : ∀ y ∈ S ⊓ L, y ^ 2 = 1 → v * y * v⁻¹ ∈ S ⊓ L := by
    intro y hy hy2
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, mul_inv_cancel]
      exact one_mem _
    obtain ⟨g, -, hg⟩ := hσ.exists_conj_eq_z hKF hy hy2 hy1
    have hτT : v * y * v⁻¹ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
      (mem_normalizer_iff.mp (hV.le hv) y).mp (hDT hy)
    have hτ2 : (v * y * v⁻¹) ^ 2 = 1 := by
      have : (v * y * v⁻¹) ^ 2 = v * y ^ 2 * v⁻¹ := by
        rw [sq, sq]
        group
      rw [this, hy2, mul_one, mul_inv_cancel]
    refine hσ.mem_D_of_conj_eq_z hKF hKC hV hSV hST hSV2 hv₀ hv₀T hτT hτ2 (g := g * v⁻¹) ?_
    rw [← hg]
    group
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁2, hy₂2, rfl⟩ := hσ.exists_mul_of_sq_eq_one hd
  have : v * (y₁ * y₂) * v⁻¹ = (v * y₁ * v⁻¹) * (v * y₂ * v⁻¹) := by group
  rw [this]
  exact mul_mem (key y₁ hy₁ hy₁2) (key y₂ hy₂ hy₂2)

theorem conj_ne_of_not_mem_T [Finite X] (hσ : Setup42 h hS w z) {f : X} (hfS : f ∈ S)
    (hfT : f ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) {y : X} (hyD : y ∈ S ⊓ L) (hy2 : y ^ 2 = 1)
    (hyz : y ∉ zpowers z) {c : X} (hc : c ∈ S ⊓ L) : f⁻¹ * y * f ≠ c⁻¹ * y * c := by
  intro heq
  have hdata := hσ.lift.data
  have hR := h.map_rho_inf_innAut hS
  have hfH := hS.le hfS
  have hα : h.rho ⟨f, hfH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho :=
    ⟨⟨f, hfH⟩, hfS, rfl⟩
  have hα' : h.rho ⟨f, hfH⟩ ∉ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊔ zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) := fun h' =>
    hfT (hσ.mem_T_of_rho_mem hfS h')
  have hne : (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ≠
      ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
        zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) := fun heq' => hα' (heq' ▸ hα)
  have hyS : y ∈ S := hyD.1
  have hyH := hS.le hyS
  have hyR : h.rho ⟨y, hyH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L) := by
    rw [hR]
    exact ⟨⟨y, hyH⟩, hyD, rfl⟩
  have hρy2 : h.rho ⟨y, hyH⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyH⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 :=
      Subtype.ext (by simpa using hy2)
    rw [this, map_one]
  have hyC : h.rho ⟨y, hyH⟩ ∉ centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L) : Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) := by
    intro hyC
    apply hyz
    rw [← hσ.center_D]
    refine Subgroup.mem_inf.mpr ⟨hyD, mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hdR : h.rho ⟨d, hS.le hd.1⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
        innAut (Bar L) := by
      rw [hR]
      exact ⟨⟨d, hS.le hd.1⟩, hd, rfl⟩
    have := mem_centralizer_iff.mp hyC _ hdR
    exact (h.commute_of_rho_commute hS hyS hd.1 hyD.2 this.symm).symm
  have hswap := hdata.swap_of_ne hne _ hα hα' _ hyR hρy2 hyC
  have hcH := hS.le hc.1
  have hcR : h.rho ⟨c, hcH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L) := by
    rw [hR]
    exact ⟨⟨c, hcH⟩, hc, rfl⟩
  apply hswap _ hcR
  have h3 : (⟨f⁻¹ * y * f, hS.le (S.mul_mem (S.mul_mem (S.inv_mem hfS) hyS) hfS)⟩ :
      ↥(centralizer ({t} : Set X))) =
      ⟨c⁻¹ * y * c, hS.le (S.mul_mem (S.mul_mem (S.inv_mem hc.1) hyS) hc.1)⟩ :=
    Subtype.ext heq
  have h1 : (⟨f⁻¹ * y * f, hS.le (S.mul_mem (S.mul_mem (S.inv_mem hfS) hyS) hfS)⟩ :
      ↥(centralizer ({t} : Set X))) = (⟨f, hfH⟩)⁻¹ * ⟨y, hyH⟩ * ⟨f, hfH⟩ := rfl
  have h2 : (⟨c⁻¹ * y * c, hS.le (S.mul_mem (S.mul_mem (S.inv_mem hc.1) hyS) hc.1)⟩ :
      ↥(centralizer ({t} : Set X))) = (⟨c, hcH⟩)⁻¹ * ⟨y, hyH⟩ * ⟨c, hcH⟩ := rfl
  have := congrArg h.rho h3
  rw [h1, h2, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv] at this
  exact this

theorem sq_mem_T_of_relIndex [Finite X] (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hST : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2)
    (hSV2 : S.relIndex V = 2) {v₀ : X} (hv₀ : v₀ ∈ V) :
    v₀ ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  by_contra hv₀T
  obtain ⟨m, hm, ⟨e⟩⟩ := hσ.dihedral
  set y₀ : ↥(S ⊓ L) := e.symm (DihedralGroup.sr 0) with hy₀
  have hy₀2 : (y₀ : X) ^ 2 = 1 := by
    have : y₀ ^ 2 = 1 := by
      apply e.injective
      rw [sq, map_mul, hy₀, MulEquiv.apply_symm_apply, DihedralGroup.sr_mul_sr, sub_self,
        DihedralGroup.r_zero, map_one]
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hy₀z : (y₀ : X) ∉ zpowers z := by
    intro h'
    rcases eq_one_or_eq_of_mem_zpowers hσ.z_order h' with h1 | h1
    · have : y₀ = 1 := Subtype.ext h1
      rw [hy₀, MulEquiv.map_eq_one_iff] at this
      exact absurd (this.trans DihedralGroup.one_def) fun h'' => by cases h''
    · rw [← hσ.coe_symm_r_half hm e] at h1
      have : y₀ = e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := Subtype.ext h1
      rw [hy₀] at this
      exact absurd (e.symm.injective this) fun h'' => by cases h''
  have hDV : ∀ d ∈ S ⊓ L, v₀ * d * v₀⁻¹ ∈ S ⊓ L := fun d hd =>
    hσ.conj_mem_D_of_mem_V hKF hKC hV hSV hST hSV2 hv₀ hv₀T hv₀ hd
  have hDV' : ∀ d ∈ S ⊓ L, v₀⁻¹ * d * v₀ ∈ S ⊓ L := fun d hd => by
    have := hσ.conj_mem_D_of_mem_V hKF hKC hV hSV hST hSV2 hv₀ hv₀T (inv_mem hv₀) hd
    rwa [inv_inv] at this
  obtain ⟨c, hc, hceq⟩ := exists_conj_sq_eq e hm hσ.center_D hDV' hDV y₀.2 hy₀2 hy₀z
  exact hσ.conj_ne_of_not_mem_T (sq_mem_of_relIndex_two hSV2 hv₀) hv₀T y₀.2 hy₀2 hy₀z hc hceq

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
