module

public import CFSG.LargeExtraspecial.AS35CS64Exist
public import CFSG.LargeExtraspecial.FS65Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem two_pow_le_card_of_trivialInter_gen (hn : 3 ≤ S.width)
    (H : ∀ g t : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa g → t = 1)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z) :
    2 ^ (S.width + 1) ≤ Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  set T := S.conjBy g with hT
  have hTz : T.z = x := by rw [hT, conjBy_z, hgx]
  have hTn : 3 ≤ T.width := by rw [hT, S.width_conjBy]; exact hn
  have hWT := S.weaklyClosed_conjBy hW g
  have hzMT : S.z ∈ T.M := by rw [T.mem_M_iff, hTz]; exact (S.z_comm hxM).symm
  have hne : g * S.z * g⁻¹ ≠ S.z := by rw [hgx]; exact hxz
  have hzQa : S.z ∉ S.Qa g := S.z_not_mem_Qa hW hne
  have hzQT : (⟨S.z, hzMT⟩ : T.M) ∉ T.Q := fun h => hzQa ⟨_, h, rfl⟩
  have hzT : g⁻¹ * T.z * g⁻¹⁻¹ = S.z := by rw [hTz, ← hgx]; group
  set τ : T.Qt ≃ₗ[ZMod 2] T.Qt := ((T.ρ ⟨S.z, hzMT⟩ : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) with hτ
  have hτ2 : τ * τ = 1 := T.ρ_mul_self hzMT (by rw [pow_two]; exact S.z_mul_z)
  have hOτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup T.q := (T.ρ ⟨S.z, hzMT⟩).2
  obtain ⟨u, hu, hu0, hqu⟩ := T.exists_singular_of_two_le
    (fun u hu v hv => polar_commSpace_eq_zero hOτ hτ2 hu hv)
    (T.two_le_finrank_commSpace_of_conj (by omega) (x := ⟨S.z, hzMT⟩) hzT hzQT)
  obtain ⟨v, hv⟩ := mem_commSpace.mp hu
  obtain ⟨e, heT, rfl⟩ := T.exists_cl v
  have hkT : e * S.z * e⁻¹ * S.z⁻¹ ∈ T.QG := T.comm_mem_QG hzMT heT
  have hkcl : T.cl (e * S.z * e⁻¹ * S.z⁻¹) = u := by
    rw [T.cl_comm hzMT heT, ← hv, sub_eq_add_vec (ZMod 2), add_comm]
  have hk2 : e * S.z * e⁻¹ * S.z⁻¹ * (e * S.z * e⁻¹ * S.z⁻¹) = 1 := by
    have := (T.q_cl_eq_zero_iff hkT).mp (by rw [hkcl]; exact hqu)
    rwa [pow_two] at this
  have hk1 : e * S.z * e⁻¹ * S.z⁻¹ ≠ 1 := fun h => hu0 (by rw [← hkcl, h, T.cl_one])
  have hkx : e * S.z * e⁻¹ * S.z⁻¹ ≠ x := fun h => hu0 (by rw [← hkcl, h, ← hTz, T.cl_z])
  have hkz : e * S.z * e⁻¹ * S.z⁻¹ * S.z = S.z * (e * S.z * e⁻¹ * S.z⁻¹) := by
    have hinv := conj_comm_eq_inv S.z_mul_z e
    rw [inv_eq_of_mul_eq_one_right hk2] at hinv
    symm
    calc S.z * (e * S.z * e⁻¹ * S.z⁻¹) =
        S.z * (e * S.z * e⁻¹ * S.z⁻¹) * S.z⁻¹ * S.z := by group
      _ = e * S.z * e⁻¹ * S.z⁻¹ * S.z := by rw [hinv]
  set k := e * S.z * e⁻¹ * S.z⁻¹ with hk
  have hy : e * S.z * e⁻¹ = k * S.z := by rw [hk]; group
  have hkM : k ∈ S.M := S.mem_M_iff.mpr hkz
  have hyM : e * S.z * e⁻¹ ∈ S.M := by rw [hy]; exact mul_mem hkM S.z_mem_M
  have hlam : ∀ c ∈ S.QG, c * (e * S.z * e⁻¹) * c⁻¹ ≠ e * S.z * e⁻¹ * S.z := by
    intro c _ hc
    have hk' : (c * e * g⁻¹) * T.z * (c * e * g⁻¹)⁻¹ = k := by
      calc (c * e * g⁻¹) * T.z * (c * e * g⁻¹)⁻¹ = c * (e * S.z * e⁻¹) * c⁻¹ := by
            rw [hTz, ← hgx]; group
        _ = e * S.z * e⁻¹ * S.z := hc
        _ = k := by rw [hy, mul_assoc k S.z S.z, S.z_mul_z, mul_one]
    have h1 := hWT _ (hk' ▸ hkT)
    rw [hk', hTz] at h1
    exact hkx h1
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨e * S.z * e⁻¹, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
    with hσ
  have hσ2 : σ * σ = 1 := S.ρ_mul_self hyM (by rw [pow_two]; exact S.conj_mul_self e)
  have hfix : S.clPre (fixSpace σ) ≤ S.QG ⊓ centralizer ({x} : Set G) := by
    intro a ha
    obtain ⟨haQ, hacl⟩ := S.mem_clPre.mp ha
    have hay := S.commute_of_fix hyM hlam haQ (mem_fixSpace.mp hacl)
    have haz := S.z_comm_QG haQ
    have hak : a * k = k * a := by
      rw [hy] at hay
      have h1 : a * k * S.z = k * a * S.z := by
        calc a * k * S.z = a * (k * S.z) := by group
          _ = k * S.z * a := hay
          _ = k * (S.z * a) := by group
          _ = k * (a * S.z) := by rw [haz]
          _ = k * a * S.z := by group
      exact mul_right_cancel h1
    exact mem_inf.mpr ⟨haQ, mem_centralizer_singleton_iff.mpr
      (S.commute_of_mem_centralizer H hgx hxM hkT hk1 haQ hak)⟩
  have hdim := S.width_le_finrank_fixSpace hσ2
  calc 2 ^ (S.width + 1) = 2 * 2 ^ S.width := by rw [pow_succ, mul_comm]
    _ ≤ 2 * 2 ^ finrank (ZMod 2) (fixSpace σ) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hdim)
    _ = Nat.card (S.clPre (fixSpace σ)) := by rw [S.card_clPre, S.card_submodule]
    _ ≤ Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) := Subgroup.card_le_of_le hfix

theorem mem_of_commute_of_trivialInter_gen (hn : 3 ≤ S.width)
    (H : ∀ g t : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa g → t = 1)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z) {e : G}
    (heQ : e ∈ S.QG) (he : ∀ a ∈ S.QG ⊓ centralizer ({x} : Set G), e * a = a * e) :
    e ∈ S.QG ⊓ centralizer ({x} : Set G) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set A : Subgroup G := S.QG ⊓ centralizer ({x} : Set G) with hA
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨haQ, hac⟩ := mem_inf.mp ha
    rw [← pow_two]
    exact S.sq_eq_one_of_trivialInter H hW hgx hxM hxz haQ (mem_centralizer_singleton_iff.mp hac)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hab := hsq (a * b) (mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have hle := S.card_le_of_commute (inf_le_left : A ≤ S.QG) hcomm
  have hge := S.two_pow_le_card_of_trivialInter_gen hn H hW hgx hxM hxz
  have hzA : S.z ∈ A := mem_inf.mpr ⟨S.z_mem_QG,
    mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm⟩
  have hcardA : Nat.card A = 2 * 2 ^ finrank (ZMod 2) (S.clSub A) := by
    have h1 := S.card_clPre (S.clSub A)
    rwa [S.clPre_clSub inf_le_left hzA, S.card_submodule] at h1
  have hdimA : finrank (ZMod 2) (S.clSub A) = S.width := by
    have h1 : 2 ^ (finrank (ZMod 2) (S.clSub A) + 1) = 2 ^ (S.width + 1) := by
      rw [pow_succ, mul_comm, ← hcardA]
      exact le_antisymm hle hge
    have := Nat.pow_right_injective le_rfl h1
    omega
  have hC := S.centralizer_inf_QG_eq_clPre (inf_le_left : A ≤ S.QG)
  have hcardC : Nat.card ↥(S.QG ⊓ centralizer (A : Set G)) = 2 ^ (S.width + 1) := by
    rw [hC, S.card_clPre, S.card_submodule,
      LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, hdimA,
      S.finrank_Qt_eq_two_mul_width, pow_succ, mul_comm]
    congr 2
    omega
  have hAC : A ≤ S.QG ⊓ centralizer (A : Set G) := fun a ha =>
    mem_inf.mpr ⟨(mem_inf.mp ha).1, mem_centralizer_iff.mpr fun b hb => hcomm b hb a ha⟩
  have hAeq : A = S.QG ⊓ centralizer (A : Set G) :=
    Subgroup.eq_of_le_of_card_ge hAC (by rw [hcardC]; exact hge)
  rw [hAeq]
  exact mem_inf.mpr ⟨heQ, mem_centralizer_iff.mpr fun a ha => (he a ha).symm⟩

theorem comm_mem_of_trivialInter_gen (hn : 3 ≤ S.width)
    (H : ∀ g t : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa g → t = 1)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    {g x : G} (hgx : g * S.z * g⁻¹ = x) (hxM : x ∈ S.M) (hxz : x ≠ S.z) {b : G}
    (hbx : b ∈ S.Qa g) (hbz : b * S.z = S.z * b) {e : G} (heQ : e ∈ S.QG) :
    b * e * b⁻¹ * e⁻¹ ∈ S.QG ⊓ centralizer ({x} : Set G) := by
  have hbM : b ∈ S.M := S.mem_M_iff.mpr hbz
  have hgM : g * S.z * g⁻¹ ∈ S.M := by rw [hgx]; exact hxM
  have hne : g * S.z * g⁻¹ ≠ S.z := by rw [hgx]; exact hxz
  have hwQ : b * e * b⁻¹ * e⁻¹ ∈ S.QG := mul_mem (S.conj_mem_QG hbM heQ) (inv_mem heQ)
  refine S.mem_of_commute_of_trivialInter_gen hn H hW hgx hxM hxz hwQ fun a ha => ?_
  obtain ⟨haQ, hac⟩ := mem_inf.mp ha
  have hax : a * x = x * a := mem_centralizer_singleton_iff.mp hac
  have haT : a ∈ (S.conjBy g).M := by
    rw [(S.conjBy g).mem_M_iff, conjBy_z, hgx]
    exact hax
  have hab : b * a * b⁻¹ = a := by
    have hkQ : b * a * b⁻¹ * a⁻¹ ∈ S.QG := mul_mem (S.conj_mem_QG hbM haQ) (inv_mem haQ)
    have hkT : b * a * b⁻¹ * a⁻¹ ∈ S.Qa g := by
      have := mul_mem hbx ((S.conjBy g).conj_mem_QG haT (inv_mem hbx))
      simpa [mul_assoc] using this
    have h1 := H g _ hgM hne hkQ hkT
    calc b * a * b⁻¹ = b * a * b⁻¹ * a⁻¹ * a := by group
      _ = a := by rw [h1, one_mul]
  rw [← S.polar_cl_eq_zero_iff hwQ haQ]
  have e1 : S.cl (b * e * b⁻¹ * e⁻¹) = ((S.ρ ⟨b, hbM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) +
      S.cl e := by
    rw [S.cl_mul (S.conj_mem_QG hbM heQ) (inv_mem heQ), S.cl_inv heQ, S.ρ_cl ⟨b, hbM⟩ heQ]
  have e2 : ((S.ρ ⟨b, hbM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) = S.cl a := by
    rw [S.ρ_cl ⟨b, hbM⟩ haQ]
    exact congrArg S.cl hab
  have e3 : polar S.q (((S.ρ ⟨b, hbM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e)) (S.cl a) =
      polar S.q (S.cl e) (S.cl a) := by
    conv_lhs => rw [← e2]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ ⟨b, hbM⟩).2 _ _
  rw [e1, polar_add_left, e3]
  exact CharTwo.add_self_eq_zero _

theorem exists_inf_Qa_ne_one_gen (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (hiso : ∃ g : G, g * S.z * g⁻¹ ∈ S.M ∧ g * S.z * g⁻¹ ≠ S.z) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.M ∧ g * S.z * g⁻¹ ≠ S.z ∧ ∃ t ∈ S.QG, t ∈ S.Qa g ∧ t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have H : ∀ g t : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ≠ S.z → t ∈ S.QG → t ∈ S.Qa g →
      t = 1 := fun g t h1 h2 h3 h4 => hcon g h1 h2 t h3 h4
  obtain ⟨g, hgM, hgne⟩ := hiso
  set x := g * S.z * g⁻¹ with hx
  have hgx : g * S.z * g⁻¹ = x := rfl
  set A : Subgroup G := S.QG ⊓ centralizer ({x} : Set G) with hA
  have hsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨haQ, hac⟩ := mem_inf.mp ha
    rw [← pow_two]
    exact S.sq_eq_one_of_trivialInter H hW hgx hgM hgne haQ (mem_centralizer_singleton_iff.mp hac)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hab := hsq (a * b) (mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  have hAle := S.card_le_of_commute (inf_le_left : A ≤ S.QG) hcomm
  set T := S.conjBy g with hT
  have hTz : T.z = x := by rw [hT, conjBy_z]
  have hTn : 3 ≤ T.width := by rw [hT, S.width_conjBy]; exact hn
  have hzT : g⁻¹ * T.z * g⁻¹⁻¹ = S.z := by rw [hTz, hx]; group
  have hzMT : S.z ∈ T.M := by rw [T.mem_M_iff, hTz]; exact (S.z_comm hgM).symm
  have hzneT : S.z ≠ T.z := by rw [hTz]; exact hgne.symm
  have hBge : 2 ^ (S.width + 1) ≤ Nat.card ↥(S.Qa g ⊓ centralizer ({S.z} : Set G)) := by
    have h1 := T.two_pow_le_card_of_trivialInter_gen hTn (S.trivialInter_conjBy H g)
      (S.weaklyClosed_conjBy hW g) hzT hzMT hzneT
    rwa [hT, S.width_conjBy] at h1
  obtain ⟨e₀, he₀Q, he₀A⟩ : ∃ e ∈ S.QG, e ∉ A := by
    by_contra h
    push Not at h
    have h1 : Nat.card S.QG ≤ Nat.card A := Subgroup.card_le_of_le h
    rw [S.card_QG_eq_card_Q, S.card_Q_eq] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (h1.trans hAle)
    omega
  obtain ⟨a₀, ha₀A, ha₀e⟩ : ∃ a ∈ A, e₀ * a ≠ a * e₀ := by
    by_contra h
    push Not at h
    exact he₀A (S.mem_of_commute_of_trivialInter_gen hn H hW hgx hgM hgne he₀Q h)
  obtain ⟨e, heQ, heA, he2⟩ : ∃ e ∈ S.QG, e ∉ A ∧ e * e = 1 := by
    rcases S.sq_eq_one_or_z he₀Q with h | h
    · exact ⟨e₀, he₀Q, he₀A, by rwa [pow_two] at h⟩
    · have ha₀Q : a₀ ∈ S.QG := (mem_inf.mp ha₀A).1
      refine ⟨e₀ * a₀, mul_mem he₀Q ha₀Q, fun h' => he₀A ?_, ?_⟩
      · have := mul_mem h' (inv_mem ha₀A)
        simpa using this
      · have hae : a₀ * e₀ = S.z * (e₀ * a₀) := by
          rcases S.mul_comm_or ha₀Q he₀Q with h' | h'
          · exact absurd h'.symm ha₀e
          · exact h'
        have hze : e₀ * S.z = S.z * e₀ := S.z_comm_QG he₀Q
        calc e₀ * a₀ * (e₀ * a₀) = e₀ * (a₀ * e₀) * a₀ := by group
          _ = S.z * (e₀ * e₀) * (a₀ * a₀) := by rw [hae, ← mul_assoc e₀ S.z, hze]; group
          _ = 1 := by rw [← pow_two, h, hsq a₀ ha₀A, S.z_mul_z, one_mul]
  have hmemA : ∀ b : ↥(S.Qa g ⊓ centralizer ({S.z} : Set G)),
      (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ A := fun b =>
    S.comm_mem_of_trivialInter_gen hn H hW hgx hgM hgne (mem_inf.mp b.2).1
      (mem_centralizer_singleton_iff.mp (mem_inf.mp b.2).2) heQ
  let φ : ↥(S.Qa g ⊓ centralizer ({S.z} : Set G)) → ↥A := fun b => ⟨_, hmemA b⟩
  have hinj : Function.Injective φ := by
    intro b b' hbb
    have h1 : (b : G) * e * (b : G)⁻¹ * e⁻¹ = (b' : G) * e * (b' : G)⁻¹ * e⁻¹ :=
      congrArg Subtype.val hbb
    have h2 : ((b' : G)⁻¹ * b) * e = e * ((b' : G)⁻¹ * b) := by
      have h3 : (b : G) * e * (b : G)⁻¹ = (b' : G) * e * (b' : G)⁻¹ := mul_right_cancel h1
      calc ((b' : G)⁻¹ * b) * e = (b' : G)⁻¹ * ((b : G) * e * (b : G)⁻¹) * b := by group
        _ = (b' : G)⁻¹ * ((b' : G) * e * (b' : G)⁻¹) * b := by rw [h3]
        _ = e * ((b' : G)⁻¹ * b) := by group
    by_contra hne
    have hk1 : (b' : G)⁻¹ * b ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      calc (b : G) = (b' : G) * ((b' : G)⁻¹ * b) := by group
        _ = b' := by rw [h, mul_one]
    have hkx : (b' : G)⁻¹ * b ∈ S.Qa g :=
      mul_mem (inv_mem (mem_inf.mp b'.2).1) (mem_inf.mp b.2).1
    have hex := S.commute_of_mem_centralizer H hgx hgM hkx hk1 heQ h2.symm
    exact heA (mem_inf.mpr ⟨heQ, mem_centralizer_singleton_iff.mpr hex⟩)
  have hbij := hinj.bijective_of_nat_card_le (hAle.trans hBge)
  have hcommA : ∀ a ∈ A, e * a = a * e := by
    intro a ha
    obtain ⟨b, hb⟩ := hbij.2 ⟨a, ha⟩
    have h1 : (b : G) * e * (b : G)⁻¹ * e⁻¹ = a := congrArg Subtype.val hb
    have h2 : a * e * (a * e) = 1 := by
      rw [← h1]
      calc (b : G) * e * (b : G)⁻¹ * e⁻¹ * e * ((b : G) * e * (b : G)⁻¹ * e⁻¹ * e) =
          (b : G) * (e * e) * (b : G)⁻¹ := by group
        _ = 1 := by rw [he2]; group
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    calc e * a = (a * e)⁻¹ := by rw [mul_inv_rev, ha', he']
      _ = a * e := (eq_inv_of_mul_eq_one_left h2).symm
  exact heA (S.mem_of_commute_of_trivialInter_gen hn H hW hgx hgM hgne heQ hcommA)


theorem exists_four_le_card_inf_Qa_gen (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (hiso : ∃ g : G, g * S.z * g⁻¹ ∈ S.M ∧ g * S.z * g⁻¹ ≠ S.z) :
    ∃ h : G, h * S.z * h⁻¹ ∈ S.M ∧ h * S.z * h⁻¹ ≠ S.z ∧ 4 ≤ Nat.card ↥(S.QG ⊓ S.Qa h) := by
  obtain ⟨g, hgM, hgne, t, htQ, htx, ht1⟩ := S.exists_inf_Qa_ne_one_gen hn hW hiso
  exact ⟨g, hgM, hgne, S.four_le_card_inf_Qa_gen hn hW rfl hgM hgne htQ htx ht1⟩

end Setting

end CFSG.LargeExtraspecial
