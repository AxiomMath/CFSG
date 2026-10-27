module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.GaloisSeven

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

section Map

variable {G H : Type*} [Group G] [Group H] {p n : ℕ}

theorem HeisCfg.map {x y : Fin n → G} {z : G} (f : G →* H) (h : HeisCfg p n x y z)
    (hfz : f z ≠ 1) :
    HeisCfg p n (fun i => f (x i)) (fun i => f (y i)) (f z) where
  xp i := by rw [← map_pow, h.xp i, map_one]
  zp := by rw [← map_pow, h.zp, map_one]
  zx i := by
    simp only [← map_mul]
    exact congrArg f (h.zx i)
  zy i := by
    simp only [← map_mul]
    exact congrArg f (h.zy i)
  yx i := by
    simp only [← map_inv, ← map_mul]
    exact congrArg f (h.yx i)
  xx i j := by
    simp only [← map_mul]
    exact congrArg f (h.xx i j)
  yy i j hij := by
    simp only [← map_mul]
    exact congrArg f (h.yy i j hij)
  xy i j hij := by
    simp only [← map_mul]
    exact congrArg f (h.xy i j hij)
  z1 := hfz

end Map

section Lift

variable {L S : Type*} [Group L] [Group S]

theorem eq_of_map_eq_of_pow_eq_one (π : L →* S) (hK : π.ker ≤ Subgroup.center L) {p : ℕ}
    [Fact p.Prime] (hKp : ¬ p ∣ Nat.card π.ker) {u v : L} (hu : u ^ p = 1) (hv : v ^ p = 1)
    (huv : π u = π v) : u = v := by
  set k : L := v⁻¹ * u with hk
  have hkker : k ∈ π.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_inv, huv, inv_mul_cancel]
  have hkc : k ∈ Subgroup.center L := hK hkker
  have hcomm : Commute v k := Subgroup.mem_center_iff.1 hkc v
  have huvk : u = v * k := by rw [hk]; group
  have hkp : k ^ p = 1 := by
    have : u ^ p = v ^ p * k ^ p := by rw [huvk]; exact hcomm.mul_pow p
    rw [hu, hv, one_mul] at this
    exact this.symm
  have hdvd1 : orderOf k ∣ p := orderOf_dvd_of_pow_eq_one hkp
  have hdvd2 : orderOf k ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨k, hkker⟩ : π.ker)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd1 with h | h
  · have : k = 1 := orderOf_eq_one_iff.1 h
    rw [hk] at this
    exact (inv_mul_eq_one.1 this).symm
  · exact absurd (h ▸ hdvd2) hKp

theorem exists_map_eq_pow_eq_one (π : L →* S) (hπ : Function.Surjective π) {p : ℕ}
    [Fact p.Prime] (hKp : ¬ p ∣ Nat.card π.ker) {a : S} (ha : a ^ p = 1) :
    ∃ l : L, π l = a ∧ l ^ p = 1 := by
  obtain ⟨l, rfl⟩ := hπ a
  set m := Nat.card π.ker with hm
  have hcop : Nat.Coprime m p :=
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hKp).symm
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Fact.out : p.Prime).one_lt
  refine ⟨l ^ (m * t), ?_, ?_⟩
  · have h1 : m * t = p * (m * t / p) + 1 := by
      have := Nat.div_add_mod (m * t) p
      omega
    rw [map_pow, h1, pow_add, pow_mul, ha, one_pow, one_mul, pow_one]
  · have hlp : l ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, ha]
    have hlpm : (l ^ p) ^ m = 1 := by
      have := pow_card_eq_one' (G := π.ker) (x := ⟨l ^ p, hlp⟩)
      exact congrArg Subtype.val this
    have : (l ^ (m * t)) ^ p = ((l ^ p) ^ m) ^ t := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [this, hlpm, one_pow]

variable {π : L →* S} {p : ℕ}

private theorem conj_pow_eq_one {a b : L} (ha : a ^ p = 1) : (b⁻¹ * a * b) ^ p = 1 := by
  have := conj_pow (a := b⁻¹) (b := a) (i := p)
  rw [inv_inv] at this
  rw [this, ha]
  group

private theorem conj_pow_eq_one' {a b : L} (ha : a ^ p = 1) : (b * a * b⁻¹) ^ p = 1 := by
  have := conj_pow (a := b) (b := a) (i := p)
  rw [this, ha]
  group

private theorem comm_of_map (hK : π.ker ≤ Subgroup.center L) [Fact p.Prime]
    (hKp : ¬ p ∣ Nat.card π.ker) {a b : L} (ha : a ^ p = 1) (hab : π a * π b = π b * π a) :
    a * b = b * a := by
  have h : b⁻¹ * a * b = a := by
    refine eq_of_map_eq_of_pow_eq_one π hK hKp (conj_pow_eq_one ha) ha ?_
    rw [map_mul, map_mul, map_inv, mul_assoc, hab, inv_mul_cancel_left]
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [h]

theorem HeisCfg.exists_lift (π : L →* S) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center L) {p n : ℕ} [Fact p.Prime] (hKp : ¬ p ∣ Nat.card π.ker)
    {x y : Fin n → S} {z : S} (h : HeisCfg p n x y z) (hy : ∀ i, y i ^ p = 1) :
    ∃ (x' y' : Fin n → L) (z' : L), HeisCfg p n x' y' z' ∧ (∀ i, π (x' i) = x i) ∧
      (∀ i, π (y' i) = y i) ∧ π z' = z ∧ ∀ i, y' i ^ p = 1 := by
  choose x' hx'1 hx'2 using fun i => exists_map_eq_pow_eq_one π hπ hKp (h.xp i)
  choose y' hy'1 hy'2 using fun i => exists_map_eq_pow_eq_one π hπ hKp (hy i)
  obtain ⟨z', hz'1, hz'2⟩ := exists_map_eq_pow_eq_one π hπ hKp h.zp
  refine ⟨x', y', z', ?_, hx'1, hy'1, hz'1, hy'2⟩
  have hcomm : ∀ {a b : L}, a ^ p = 1 → π a * π b = π b * π a → a * b = b * a :=
    fun ha hab => comm_of_map hK hKp ha hab
  have hzx : ∀ i, x' i * z' = z' * x' i := fun i =>
    hcomm (hx'2 i) (by rw [hx'1, hz'1]; exact h.zx i)
  exact
    { xp := hx'2
      zp := hz'2
      zx := hzx
      zy := fun i => hcomm (hy'2 i) (by rw [hy'1, hz'1]; exact h.zy i)
      yx := fun i => by
        refine eq_of_map_eq_of_pow_eq_one π hK hKp (conj_pow_eq_one (hx'2 i))
          ?_ ?_
        · have hc : Commute (x' i) z' := hzx i
          rw [hc.mul_pow, hx'2 i, hz'2, one_mul]
        · rw [map_mul, map_mul, map_mul, map_inv, hx'1, hy'1, hz'1]
          exact h.yx i
      xx := fun i j => hcomm (hx'2 i) (by rw [hx'1, hx'1]; exact h.xx i j)
      yy := fun i j hij => hcomm (hy'2 i) (by rw [hy'1, hy'1]; exact h.yy i j hij)
      xy := fun i j hij => hcomm (hx'2 i) (by rw [hx'1, hy'1]; exact h.xy i j hij)
      z1 := fun hz1 => h.z1 (by rw [← hz'1, hz1, map_one]) }

end Lift

section Center

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {S : Type} [Group S]

noncomputable def centerQuotientHom (e : CQ L ≃* S) : ↥L →* S :=
  (e : CQ L →* S).comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem centerQuotientHom_surjective (e : CQ L ≃* S) :
    Function.Surjective (centerQuotientHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_centerQuotientHom (e : CQ L ≃* S) :
    (centerQuotientHom e).ker = Subgroup.center ↥L := by
  ext k
  rw [MonoidHom.mem_ker]
  show e (QuotientGroup.mk k) = 1 ↔ k ∈ Subgroup.center ↥L
  rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem two_pow_le_card_of_heisCfg_centerQuotient [Finite W] (hW : ∀ w : W, w * w = 1)
    (e : CQ L ≃* S) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {x y : Fin n → S} {z : S}
    (h : HeisCfg p n x y z) (hy : ∀ i, y i ^ p = 1) :
    2 ^ (p ^ n * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  have hK := ker_centerQuotientHom e
  obtain ⟨x', y', z', h', -, -, -, -⟩ := HeisCfg.exists_lift (centerQuotientHom e)
    (centerQuotientHom_surjective e) hK.le (by rw [hK]; exact hZ) h hy
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have h2 := two_pow_le_card_imgT_of_heisCfg hW hp2 (h'.map L.subtype hz')
  exact h2.trans (Subgroup.card_le_card_group _)

theorem two_pow_le_card_of_heisCfg_centerQuotient_of_inv_seven [Finite W]
    (hW : ∀ w : W, w * w = 1) (e : CQ L ≃* S) {n : ℕ}
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center ↥L)) {x y : Fin n → S} {z : S}
    (h : HeisCfg 7 n x y z) (hy : ∀ i, y i ^ 7 = 1) {g : S} (hg : g * z * g⁻¹ = z⁻¹) :
    2 ^ (2 * (7 ^ n * 3)) ≤ Nat.card W := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK := ker_centerQuotientHom e
  have hKp : ¬ 7 ∣ Nat.card (centerQuotientHom e).ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', -, -, hz'1, -⟩ := HeisCfg.exists_lift (centerQuotientHom e)
    (centerQuotientHom_surjective e) hK.le hKp h hy
  obtain ⟨g', hg'⟩ := centerQuotientHom_surjective e g
  have hinv : g' * z' * g'⁻¹ = z'⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one (centerQuotientHom e) hK.le hKp
      (conj_pow_eq_one' h'.zp) (by rw [inv_pow, h'.zp, inv_one]) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hg', hz'1]
    exact hg
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : L.subtype g' * L.subtype z' * (L.subtype g')⁻¹ = (L.subtype z')⁻¹ := by
    simp only [← map_inv, ← map_mul]
    exact congrArg L.subtype hinv
  have h2 := two_pow_le_card_imgT_of_heisCfg_of_inv_seven hW (h'.map L.subtype hz') hinv'
  exact h2.trans (Subgroup.card_le_card_group _)

theorem rank_of_heisCfg [Finite W] (hW : ∀ w : W, w * w = 1) (hirr : IsIrrOn L)
    (e : CQ L ≃* S) {ρ p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hρ : 2 * ρ < (p - 1) * p ^ n * orderOf (2 : ZMod p) + 2)
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ (x y : Fin (n + 1) → S) (z : S),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹) :
    ∀ b : MulAut W, b ∈ L → b ≠ 1 → b * b = 1 →
      2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index := by
  intro b hb hb1 hb2
  have ht2 : e (QuotientGroup.mk ⟨b, hb⟩) * e (QuotientGroup.mk ⟨b, hb⟩) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, ← map_one e, ← QuotientGroup.mk_one]
    congr 2
    exact Subtype.ext hb2
  have ht1 : e (QuotientGroup.mk ⟨b, hb⟩) ≠ 1 := by
    intro h
    apply hb1
    have h1 : (QuotientGroup.mk (⟨b, hb⟩ : ↥L) : CQ L) = 1 := e.injective (by rw [h, map_one])
    rw [QuotientGroup.eq_one_iff] at h1
    refine eq_one_of_commutes_of_sq_eq_one hW hirr (fun l hl => ?_) hb2
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨l, hl⟩)
  obtain ⟨x, y, z, h, hy, htx⟩ := hgen _ ht2 ht1
  have hK := ker_centerQuotientHom e
  have hKp : ¬ p ∣ Nat.card (centerQuotientHom e).ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', hx'1, -, -, -⟩ := HeisCfg.exists_lift (centerQuotientHom e)
    (centerQuotientHom_surjective e) hK.le hKp h hy
  have hinv : (⟨b, hb⟩ : ↥L) * x' 0 * (⟨b, hb⟩ : ↥L)⁻¹ = (x' 0)⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one (centerQuotientHom e) hK.le hKp
      (conj_pow_eq_one' (h'.xp 0)) (by rw [inv_pow, h'.xp 0, inv_one]) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hx'1]
    exact htx
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : b * L.subtype (x' 0) * b⁻¹ = (L.subtype (x' 0))⁻¹ := by
    have := congrArg L.subtype hinv
    simp only [map_mul, map_inv] at this
    exact this
  have h1 := two_pow_le_index_sq_of_heisCfg hW hp2 (h'.map L.subtype hz') hb2 hinv'
  exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 hρ

end Center

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
