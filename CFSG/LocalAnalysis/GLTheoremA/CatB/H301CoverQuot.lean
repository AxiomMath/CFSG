module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301CoverDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Solv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

variable {K S : Type} [Group K] [Group S]

theorem isSolvable_of_map_le (π : K →* S) (hker : π.ker ≤ Subgroup.center K) {H : Subgroup K}
    {X : Subgroup S} (hX : Group.IsSolvable X) (hHX : H.map π ≤ X) : Group.IsSolvable H := by
  let φ : H →* X := (π.comp H.subtype).codRestrict X fun h => hHX ⟨h, h.2, rfl⟩
  haveI : Group.IsSolvable φ.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have ha : ((a : H) : K) ∈ Subgroup.center K := hker (by
      have h1 : φ a = 1 := a.2
      have h2 := congrArg Subtype.val h1
      simpa [φ] using h2)
    exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.1 ha _).symm)
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])

theorem glaPLayer_eq_bot_of_map_le [Finite K] (π : K →* S) (hker : π.ker ≤ Subgroup.center K)
    {H : Subgroup K} {X : Subgroup S} (hX : Group.IsSolvable X) (hHX : H.map π ≤ X) :
    GLAPLayer 3 H = ⊥ := by
  haveI := isSolvable_of_map_le π hker hX hHX
  exact glaPLayer_eq_bot_of_isSolvable Nat.prime_three

section Lift

variable [Finite K]

theorem mem_of_two_elem {π : K →* S} (hker : π.ker ≤ Subgroup.center K)
    (hk3 : Nat.card π.ker = 3) {Rh : Subgroup K} (hRh2 : IsPGroup 2 Rh) {g : K}
    (hg : π g ∈ Rh.map π) {n : ℕ} (hgn : g ^ (2 ^ n) = 1) : g ∈ Rh := by
  obtain ⟨r, hr, hrg⟩ := hg
  set z := g * r⁻¹ with hz
  have hzk : z ∈ π.ker := by rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hrg, mul_inv_cancel]
  have hzc : ∀ y : K, z * y = y * z := fun y => (Subgroup.mem_center_iff.1 (hker hzk) y).symm
  have hgz : g = z * r := by rw [hz, inv_mul_cancel_right]
  obtain ⟨m, hm⟩ := hRh2 ⟨r, hr⟩
  have hrm : r ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := π.ker) (x := ⟨z, hzk⟩)
    rw [hk3] at h
    simpa using congrArg Subtype.val h
  have hcomm : Commute z r := hzc r
  have hzN : z ^ (2 ^ (n + m)) = 1 := by
    have h1 : g ^ (2 ^ (n + m)) = 1 := by rw [pow_add, pow_mul, hgn, one_pow]
    have h2 : r ^ (2 ^ (n + m)) = 1 := by rw [pow_add, mul_comm, pow_mul, hrm, one_pow]
    rw [hgz, hcomm.mul_pow, h2, mul_one] at h1
    exact h1
  have hz1 : z = 1 := by
    have hd : orderOf z ∣ Nat.gcd (2 ^ (n + m)) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzN) (orderOf_dvd_of_pow_eq_one hz3)
    have hg1 : Nat.gcd (2 ^ (n + m)) 3 = 1 :=
      Nat.Coprime.pow_left _ (by norm_num)
    rw [hg1, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  rw [hgz, hz1, one_mul]
  exact hr

theorem mem_normalizer_of_map {π : K →* S} (hker : π.ker ≤ Subgroup.center K)
    (hk3 : Nat.card π.ker = 3) {Rh : Subgroup K} (hRh2 : IsPGroup 2 Rh) {b : K}
    (hb : π b ∈ Subgroup.normalizer ((Rh.map π : Subgroup S) : Set S)) :
    b ∈ Subgroup.normalizer (Rh : Set K) := by
  have key : ∀ c : K, π c ∈ Subgroup.normalizer ((Rh.map π : Subgroup S) : Set S) →
      ∀ r ∈ Rh, c * r * c⁻¹ ∈ Rh := by
    intro c hc r hr
    obtain ⟨m, hm⟩ := hRh2 ⟨r, hr⟩
    have hrm : r ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    refine mem_of_two_elem hker hk3 hRh2 ?_ (n := m) ?_
    · rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hc (π r)).1 ⟨r, hr, rfl⟩
    · rw [conj_pow, hrm, mul_one, mul_inv_cancel]
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key b hb r, fun h => ?_⟩
  have h1 := key b⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hb) _ h
  simpa [mul_assoc] using h1

end Lift

section Cfg

variable [Finite K] [Finite S]

theorem exists_i301ACoverCfg_of_quot {row₀ row : Row} (hp₀ : row₀.prime = 3)
    (hp : row.prime = 3) (hrank : row.rank = row₀.rank) (hrexp : row.rexp = row₀.rexp)
    (hr0exp : row.r0exp = row₀.r0exp) (hKrow : RowK row 3 (⊥ : Subgroup K))
    (π : K →* S) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hk3 : Nat.card (Subgroup.center K) = 3)
    {R B₁ : Subgroup S} {d : S} (cfg : I301ARowCfg row₀ R B₁ d) (hKbot : rowKOf 3 d R = ⊥)
    (hsolvN : Group.IsSolvable
      ↥(Subgroup.centralizer ({d} : Set S) ⊓ Subgroup.normalizer (R : Set S)))
    (hsolvZ : Group.IsSolvable ↥(Subgroup.centralizer ({d} : Set S) ⊓
      Subgroup.centralizer (centerOf (rowR0Of d R) : Set S)))
    {Bh : Subgroup K} (hBh : IsElemAbelian 3 Bh) (hBhZ : Bh ⊓ Subgroup.center K = ⊥)
    (hBhmap : Bh.map π = B₁) {dh : K} (hdh : dh ∈ Bh) (hdhπ : π dh = d)
    (hI : RowI row 3 (rowIOf 3 dh)) :
    ∃ Rh : Subgroup K, I301ACoverCfg row Rh Bh dh := by
  have hkc : π.ker ≤ Subgroup.center K := hker.le
  have hk3' : Nat.card π.ker = 3 := by rw [hker, hk3]
  have hk2 : ¬ 2 ∣ Nat.card π.ker := by rw [hk3']; decide
  obtain ⟨Rh, hRh2, hRhmap, hRhinj⟩ := CatB.exists_pSubgroup_lift Nat.prime_two π hk2
    cfg.hR.1.1 (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top)
  let eR : Rh ≃* R := (CatB.mulEquivMap π hRhinj).trans (MulEquiv.subgroupCongr hRhmap)
  have hBhinj : Function.Injective (π.comp Bh.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    have hbk : (b : K) ∈ π.ker := hb
    have : (b : K) ∈ Bh ⊓ Subgroup.center K := ⟨b.2, hker ▸ hbk⟩
    rw [hBhZ, Subgroup.mem_bot] at this
    exact Subtype.ext this
  let eB : Bh ≃* B₁ := (CatB.mulEquivMap π hBhinj).trans (MulEquiv.subgroupCongr hBhmap)
  have hBhN : Bh ≤ Subgroup.normalizer (Rh : Set K) := fun b hb =>
    mem_normalizer_of_map hkc hk3' hRh2 (by rw [hRhmap]; exact cfg.hBN (hBhmap ▸ ⟨b, hb, rfl⟩))
  have hdhN : dh ∈ Subgroup.normalizer (Rh : Set K) := hBhN hdh
  have hmapC : ∀ g ∈ Subgroup.centralizer ({dh} : Set K),
      π g ∈ Subgroup.centralizer ({d} : Set S) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← hdhπ, ← map_mul, ← map_mul, hg]
  have hmapN : ∀ g ∈ Subgroup.normalizer (Rh : Set K),
      π g ∈ Subgroup.normalizer (R : Set S) := by
    intro g hg
    have h := Subgroup.le_normalizer_map π ⟨g, hg, rfl⟩
    rwa [hRhmap] at h
  have hR0map : (rowR0Of dh Rh).map π = rowR0Of d R := by
    apply le_antisymm
    · rintro _ ⟨r, ⟨hrR, hrC⟩, rfl⟩
      exact ⟨hRhmap ▸ ⟨r, hrR, rfl⟩, hmapC r hrC⟩
    · rintro t ⟨htR, htC⟩
      rw [← hRhmap] at htR
      obtain ⟨r, hrR, rfl⟩ := htR
      refine ⟨r, ⟨hrR, ?_⟩, rfl⟩
      have htC : π r ∈ Subgroup.centralizer ({d} : Set S) := htC
      have hc1 : r * dh * r⁻¹ * dh⁻¹ ∈ π.ker := by
        rw [Subgroup.mem_centralizer_singleton_iff] at htC
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hdhπ, htC]
        group
      have hc2 : r * dh * r⁻¹ * dh⁻¹ ∈ Rh := by
        have h := (Subgroup.mem_normalizer_iff.1 hdhN r⁻¹).1 (Rh.inv_mem hrR)
        have e : r * dh * r⁻¹ * dh⁻¹ = r * (dh * r⁻¹ * dh⁻¹) := by group
        rw [e]
        exact Rh.mul_mem hrR h
      have hc3 : r * dh * r⁻¹ * dh⁻¹ = 1 := by
        have h1 : (⟨_, hc2⟩ : Rh) = 1 := hRhinj (by
          simpa [MonoidHom.comp_apply] using (MonoidHom.mem_ker.1 hc1))
        exact congrArg Subtype.val h1
      show r ∈ Subgroup.centralizer ({dh} : Set K)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r * dh = r * dh * r⁻¹ * dh⁻¹ * (dh * r) := by group
        _ = dh * r := by rw [hc3, one_mul]
  have hR0inj : Function.Injective (π.comp (rowR0Of dh Rh).subtype) := by
    intro a b hab
    have h1 : (⟨a.1, a.2.1⟩ : Rh) = ⟨b.1, b.2.1⟩ := hRhinj hab
    exact Subtype.ext (by simpa using congrArg (fun x : Rh => (x : K)) h1)
  let e0 : rowR0Of dh Rh ≃* rowR0Of d R :=
    (CatB.mulEquivMap π hR0inj).trans (MulEquiv.subgroupCongr hR0map)
  have hKbot' : rowKOf 3 dh Rh = ⊥ := by
    unfold rowKOf
    refine glaPLayer_eq_bot_of_map_le π hkc hsolvN ?_
    have hle : rowIOf 3 dh ≤ Subgroup.centralizer ({dh} : Set K) := by
      unfold rowIOf GLAPLayer
      exact sSup_le fun _ hQ => hQ.1
    rintro _ ⟨g, ⟨hgI, hgN⟩, rfl⟩
    exact ⟨hmapC g (hle hgI), hmapN g hgN⟩
  have hZmap : centerOf (rowR0Of d R) ≤ (centerOf (rowR0Of dh Rh)).map π := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := ht
    obtain ⟨v, rfl⟩ := e0.surjective u
    have hu' : e0 v ∈ Subgroup.center ↥(rowR0Of d R) := hu
    refine ⟨v, ⟨v, ?_, rfl⟩, rfl⟩
    show v ∈ Subgroup.center ↥(rowR0Of dh Rh)
    rw [Subgroup.mem_center_iff] at hu' ⊢
    intro w
    apply e0.injective
    rw [map_mul, map_mul]
    exact hu' (e0 w)
  have hK6' : GLAPLayer 3 (Subgroup.centralizer ({dh} : Set K) ⊓
      Subgroup.centralizer (centerOf (rowR0Of dh Rh) : Set K)) = ⊥ := by
    refine glaPLayer_eq_bot_of_map_le π hkc hsolvZ ?_
    rintro _ ⟨g, ⟨hgC, hgZ⟩, rfl⟩
    refine ⟨hmapC g hgC, ?_⟩
    show π g ∈ Subgroup.centralizer (centerOf (rowR0Of d R) : Set S)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := hZmap ht
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hgZ) u hu]
  let ψ : K ⧸ Subgroup.center K ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hψ : ∀ g : K, ψ (centerQuot K g) = π g := fun g => rfl
  have hmapψ : ∀ X : Subgroup K, ((X.map (centerQuot K)).map ψ.toMonoidHom) = X.map π := by
    intro X
    rw [Subgroup.map_map]
    rfl
  refine ⟨Rh, ⟨⟨(isExtraSpec2_congr eR).2 cfg.hR.1, ?_⟩, ⟨hp ▸ hBh, ?_⟩, hBhZ, hBhN, ⟨hdh, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Nat.card_congr eR.toEquiv, cfg.hR.2, hrexp]
  · rw [Nat.card_congr eB.toEquiv, cfg.hB.2, hp, hp₀, hrank]
  · intro h1
    apply cfg.hd.2
    rw [← hdhπ, h1, map_one]
  · rw [hp]
    exact hI
  · rw [hp, hKbot']
    exact hKrow
  · rw [Nat.card_congr e0.toEquiv, cfg.hR0, hr0exp]
  · rcases cfg.hR0t with h | h
    · exact Or.inl ((isExtraSpec2_congr e0).2 h)
    · exact Or.inr ((Nat.card_congr e0.toEquiv).trans h)
  · rw [hp, hKbot', hK6']
  ·
    intro A _ _ ι hι hN hC R' hR'2 hBN hRR'
    let ι' : S →* A := ι.comp ψ.symm.toMonoidHom
    have hι' : Function.Injective ι' := hι.comp ψ.symm.injective
    have hrange : ι'.range = ι.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ.symm.surjective, ← MonoidHom.range_eq_map]
    have hcomp : ι'.comp ψ.toMonoidHom = ι := by
      ext x
      simp [ι']
    have hmapι : ∀ X : Subgroup K, (X.map π).map ι' = (X.map (centerQuot K)).map ι := by
      intro X
      rw [← hmapψ, Subgroup.map_map, hcomp]
    have hBN' : (rowKOf row₀.prime d R ⊔ B₁).map ι' ≤ Subgroup.normalizer (R' : Set A) := by
      rw [hp₀, hKbot, bot_sup_eq, ← hBhmap, hmapι]
      rw [hp, hKbot', bot_sup_eq] at hBN
      exact hBN
    have hRR'' : R.map ι' ≤ R' := by
      rw [← hRhmap, hmapι]
      exact hRR'
    have h := cfg.hMax A ι' hι' (by rw [hrange]; exact hN) (by rw [hrange]; exact hC) R' hR'2
      hBN' hRR''
    rw [h, ← hRhmap, hmapι]

end Cfg

theorem i301ARowCover_of_model {row₀ row : Row} (hp₀ : row₀.prime = 3) (hp : row.prime = 3)
    (hrank : row.rank = row₀.rank) (hrexp : row.rexp = row₀.rexp) (hr0exp : row.r0exp = row₀.r0exp)
    (hKrow : ∀ (K : Type) [Group K] [Finite K], RowK row 3 (⊥ : Subgroup K))
    (S : Type) [Group S] [Finite S]
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic row.name).Group))
    {R B₁ : Subgroup S} {d : S} (cfg : I301ARowCfg row₀ R B₁ d) (hKbot : rowKOf 3 d R = ⊥)
    (hsolvN : Group.IsSolvable
      ↥(Subgroup.centralizer ({d} : Set S) ⊓ Subgroup.normalizer (R : Set S)))
    (hsolvZ : Group.IsSolvable ↥(Subgroup.centralizer ({d} : Set S) ⊓
      Subgroup.centralizer (centerOf (rowR0Of d R) : Set S)))
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker = Subgroup.center E → Nat.card π.ker = 3 →
      ∃ Bh : Subgroup E, IsElemAbelian 3 Bh ∧ Bh ⊓ Subgroup.center E = ⊥ ∧ Bh.map π = B₁ ∧
        ∃ dh ∈ Bh, π dh = d)
    (hI : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker = Subgroup.center E → Nat.card π.ker = 3 →
      ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ → ∀ dh : E, π dh = d →
        RowI row 3 (rowIOf 3 dh)) :
    I301ARowCover row := by
  intro _ K _ _ hperf hZ3 hcat
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  obtain rfl : i = .sporadic row.name := hi
  obtain ⟨eS⟩ := hS
  let e : K ⧸ Subgroup.center K ≃* S := e₀.trans eS.symm
  let π : K →* S := e.toMonoidHom.comp (centerQuot K)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext g
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hk3 : Nat.card π.ker = 3 := by rw [hker, hZ3]
  obtain ⟨Bh, hBh, hBhZ, hBhmap, dh, hdh, hdhπ⟩ := hsplit K π hπ hker hk3
  obtain ⟨Rh, hcfg⟩ := exists_i301ACoverCfg_of_quot hp₀ hp hrank hrexp hr0exp (hKrow K) π hπ
    hker hZ3 cfg hKbot hsolvN hsolvZ hBh hBhZ hBhmap hdh hdhπ (hI K π hπ hker hk3 hperf dh hdhπ)
  exact ⟨Rh, Bh, dh, hcfg⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
